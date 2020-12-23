%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1970+1.001 : TPTP v7.4.0. Released v7.4.0.
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
% Statistics : Number of formulae       :  108 (9584 expanded)
%              Number of clauses        :   81 (3972 expanded)
%              Number of leaves         :   13 (2196 expanded)
%              Depth                    :   20
%              Number of atoms          :  548 (100129 expanded)
%              Number of equality atoms :   69 (10715 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t19_waybel_7,conjecture,(
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
                  & v2_waybel_0(X3,X1)
                  & v13_waybel_0(X3,X1)
                  & v2_waybel_7(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
               => ( ~ v1_xboole_0(X3)
                  & v2_waybel_0(X3,X2)
                  & v13_waybel_0(X3,X2)
                  & v2_waybel_7(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_7)).

fof(t4_waybel_0,axiom,(
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
                        & v2_waybel_0(X3,X1) )
                     => v2_waybel_0(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_0)).

fof(d2_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(k13_lattice3(X1,X3,X4),X2)
                        & ~ r2_hidden(X3,X2)
                        & ~ r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_7)).

fof(t26_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r1_yellow_0(X1,X3)
               => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

fof(t20_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t41_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k13_lattice3(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) )
      & ( X16 = X18
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | m1_subset_1(u1_orders_2(X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_15,negated_conjecture,(
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
                    & v2_waybel_0(X3,X1)
                    & v13_waybel_0(X3,X1)
                    & v2_waybel_7(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                 => ( ~ v1_xboole_0(X3)
                    & v2_waybel_0(X3,X2)
                    & v13_waybel_0(X3,X2)
                    & v2_waybel_7(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_waybel_7])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,
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
    & v2_waybel_0(esk7_0,esk5_0)
    & v13_waybel_0(esk7_0,esk5_0)
    & v2_waybel_7(esk7_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( v1_xboole_0(esk7_0)
      | ~ v2_waybel_0(esk7_0,esk6_0)
      | ~ v13_waybel_0(esk7_0,esk6_0)
      | ~ v2_waybel_7(esk7_0,esk6_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_19,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk5_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( u1_orders_2(esk5_0) = u1_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk6_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_29,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ l1_orders_2(X37)
      | ~ l1_orders_2(X38)
      | g1_orders_2(u1_struct_0(X37),u1_orders_2(X37)) != g1_orders_2(u1_struct_0(X38),u1_orders_2(X38))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
      | X39 != X40
      | ~ v2_waybel_0(X39,X37)
      | v2_waybel_0(X40,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_waybel_0])])])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v2_waybel_0(esk7_0,esk6_0)
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ v2_waybel_7(esk7_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk6_0) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v2_waybel_0(X4,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X4
    | ~ v2_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v12_waybel_0(X29,X27)
        | v12_waybel_0(X30,X28)
        | X29 != X30
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | g1_orders_2(u1_struct_0(X27),u1_orders_2(X27)) != g1_orders_2(u1_struct_0(X28),u1_orders_2(X28))
        | ~ l1_orders_2(X28)
        | ~ l1_orders_2(X27) )
      & ( ~ v13_waybel_0(X29,X27)
        | v13_waybel_0(X30,X28)
        | X29 != X30
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | g1_orders_2(u1_struct_0(X27),u1_orders_2(X27)) != g1_orders_2(u1_struct_0(X28),u1_orders_2(X28))
        | ~ l1_orders_2(X28)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_waybel_0])])])])).

fof(c_0_36,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v2_waybel_7(X7,X6)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(k13_lattice3(X6,X8,X9),X7)
        | r2_hidden(X8,X7)
        | r2_hidden(X9,X7)
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,X6)
        | ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v2_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,X6)
        | ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),u1_struct_0(X6))
        | v2_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,X6)
        | ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(k13_lattice3(X6,esk1_2(X6,X7),esk2_2(X6,X7)),X7)
        | v2_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,X6)
        | ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk1_2(X6,X7),X7)
        | v2_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,X6)
        | ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),X7)
        | v2_waybel_7(X7,X6)
        | v1_xboole_0(X7)
        | ~ v2_waybel_0(X7,X6)
        | ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_waybel_7])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_waybel_7(esk7_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ v2_waybel_0(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v2_waybel_0(X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_waybel_0(X1,X3)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( v13_waybel_0(X3,X4)
    | ~ v13_waybel_0(X1,X2)
    | X1 != X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_orders_2(X31)
      | ~ l1_orders_2(X32)
      | g1_orders_2(u1_struct_0(X31),u1_orders_2(X31)) != g1_orders_2(u1_struct_0(X32),u1_orders_2(X32))
      | ~ r1_yellow_0(X31,X33)
      | k1_yellow_0(X31,X33) = k1_yellow_0(X32,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_0])])])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_lattice3(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | r1_yellow_0(X22,k2_tarski(X23,X24))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk3_1(X22),u1_struct_0(X22))
        | v1_lattice3(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk4_1(X22),u1_struct_0(X22))
        | v1_lattice3(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_yellow_0(X22,k2_tarski(esk3_1(X22),esk4_1(X22)))
        | v1_lattice3(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_yellow_0])])])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_waybel_7(esk7_0,esk6_0)
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ v2_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( v2_waybel_0(esk7_0,esk6_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( v2_waybel_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( v13_waybel_0(X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v13_waybel_0(X1,X3)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X3) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v2_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_53,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_54,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_55,plain,
    ( k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ v2_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_22])]),c_0_31]),c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( v2_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_33]),c_0_33]),c_0_38]),c_0_50]),c_0_24])])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk6_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_22])])).

cnf(c_0_61,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k1_yellow_0(X1,k2_tarski(X2,X3)) = k1_yellow_0(X4,k2_tarski(X2,X3))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v13_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ v2_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_22])]),c_0_31]),c_0_48])).

fof(c_0_68,plain,(
    ! [X34,X35,X36] :
      ( ~ v3_orders_2(X34)
      | ~ v4_orders_2(X34)
      | ~ v5_orders_2(X34)
      | ~ v1_lattice3(X34)
      | ~ l1_orders_2(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | k1_yellow_0(X34,k7_domain_1(u1_struct_0(X34),X35,X36)) = k13_lattice3(X34,X35,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_yellow_0])])])).

fof(c_0_69,plain,(
    ! [X19,X20,X21] :
      ( v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X19)
      | ~ m1_subset_1(X21,X19)
      | k7_domain_1(X19,X20,X21) = k2_tarski(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_70,negated_conjecture,
    ( v13_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_23]),c_0_33]),c_0_33]),c_0_38]),c_0_61]),c_0_24])])).

cnf(c_0_71,plain,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( v2_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( k1_yellow_0(esk6_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k1_yellow_0(X2,k2_tarski(X1,esk2_2(esk6_0,esk7_0)))
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_44]),c_0_45]),c_0_22])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v13_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_58])])).

cnf(c_0_75,plain,
    ( k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k13_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_78,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_70])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_22])])).

cnf(c_0_83,negated_conjecture,
    ( k1_yellow_0(esk6_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k1_yellow_0(X2,k2_tarski(X1,esk2_2(esk6_0,esk7_0)))
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_70])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk1_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_70])])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk5_0,k7_domain_1(u1_struct_0(esk6_0),X1,X2)) = k13_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_33]),c_0_76]),c_0_77]),c_0_78]),c_0_79]),c_0_24])])).

cnf(c_0_86,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk6_0),X1,esk2_2(esk6_0,esk7_0)) = k2_tarski(X1,esk2_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k1_yellow_0(esk6_0,k2_tarski(esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0))) = k1_yellow_0(X1,k2_tarski(esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)))
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( k1_yellow_0(esk5_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k13_lattice3(esk5_0,X1,esk2_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_81])])).

cnf(c_0_89,negated_conjecture,
    ( k1_yellow_0(esk5_0,k2_tarski(esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0))) = k1_yellow_0(esk6_0,k2_tarski(esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_23]),c_0_33]),c_0_24])])).

cnf(c_0_90,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( k1_yellow_0(esk6_0,k2_tarski(X1,esk2_2(esk6_0,esk7_0))) = k13_lattice3(esk6_0,X1,esk2_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_86]),c_0_81]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_22])])).

cnf(c_0_92,negated_conjecture,
    ( k1_yellow_0(esk6_0,k2_tarski(esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0))) = k13_lattice3(esk5_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_84])])).

cnf(c_0_93,plain,
    ( r2_hidden(k13_lattice3(X1,esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_94,negated_conjecture,
    ( ~ v2_waybel_7(esk7_0,esk6_0)
    | ~ v13_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_58])])).

cnf(c_0_95,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk7_0)
    | ~ v13_waybel_0(esk7_0,esk6_0)
    | ~ v2_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_38]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_22])]),c_0_31]),c_0_48])).

cnf(c_0_97,plain,
    ( r2_hidden(X3,X1)
    | r2_hidden(X4,X1)
    | v1_xboole_0(X1)
    | ~ v2_waybel_7(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(k13_lattice3(X2,X3,X4),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_98,negated_conjecture,
    ( k13_lattice3(esk5_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)) = k13_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_84])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)),esk7_0)
    | ~ v13_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_38]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_22])]),c_0_31]),c_0_58])]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk6_0,esk7_0),esk7_0)
    | ~ v13_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_38]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_22])]),c_0_31]),c_0_58])]),c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk7_0)
    | ~ v13_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_58])])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),X1)
    | r2_hidden(esk1_2(esk6_0,esk7_0),X1)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k13_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)),X1)
    | ~ v2_waybel_7(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ v2_waybel_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_33]),c_0_33]),c_0_81]),c_0_33]),c_0_84]),c_0_76]),c_0_77]),c_0_78]),c_0_79]),c_0_24])])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk6_0,esk1_2(esk6_0,esk7_0),esk2_2(esk6_0,esk7_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_70])])).

cnf(c_0_104,negated_conjecture,
    ( v2_waybel_7(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk6_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_70])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_70])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_38]),c_0_61]),c_0_50])]),c_0_105]),c_0_106]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
