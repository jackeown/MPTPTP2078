%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1971+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:05 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  139 (2552 expanded)
%              Number of clauses        :  108 ( 834 expanded)
%              Number of leaves         :   15 ( 637 expanded)
%              Depth                    :   28
%              Number of atoms          :  923 (50358 expanded)
%              Number of equality atoms :   11 (  41 expanded)
%              Maximal formula depth    :   33 (   6 average)
%              Maximal clause size      :   70 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & v1_waybel_7(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k7_lattice3(X1))
            & v13_waybel_0(X2,k7_lattice3(X1))
            & v2_waybel_7(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_7)).

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

fof(t26_yellow_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v1_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v2_waybel_0(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_7)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(fc5_yellow_7,axiom,(
    ! [X1] :
      ( ( v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v1_lattice3(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(fc3_yellow_7,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v5_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(fc2_yellow_7,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v4_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(t21_yellow_7,axiom,(
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
             => k12_lattice3(X1,X2,X3) = k13_lattice3(k7_lattice3(X1),k8_lattice3(X1,X2),k8_lattice3(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_7)).

fof(fc1_yellow_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_orders_2(k7_lattice3(X1))
        & v3_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(dt_k8_lattice3,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k8_lattice3(X1,X2),u1_struct_0(k7_lattice3(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_lattice3)).

fof(t28_yellow_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v13_waybel_0(X2,k7_lattice3(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_7)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_7)).

fof(d6_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k8_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattice3)).

fof(dt_k9_lattice3,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(k7_lattice3(X1))) )
     => m1_subset_1(k9_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_lattice3)).

fof(d7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k7_lattice3(X1)))
         => k9_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_lattice3)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & v1_waybel_7(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,k7_lattice3(X1))
              & v13_waybel_0(X2,k7_lattice3(X1))
              & v2_waybel_7(X2,k7_lattice3(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_waybel_7])).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v2_waybel_7(X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(k13_lattice3(X11,X13,X14),X12)
        | r2_hidden(X13,X12)
        | r2_hidden(X14,X12)
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,X11)
        | ~ v13_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk3_2(X11,X12),u1_struct_0(X11))
        | v2_waybel_7(X12,X11)
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,X11)
        | ~ v13_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk4_2(X11,X12),u1_struct_0(X11))
        | v2_waybel_7(X12,X11)
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,X11)
        | ~ v13_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(k13_lattice3(X11,esk3_2(X11,X12),esk4_2(X11,X12)),X12)
        | v2_waybel_7(X12,X11)
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,X11)
        | ~ v13_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r2_hidden(esk3_2(X11,X12),X12)
        | v2_waybel_7(X12,X11)
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,X11)
        | ~ v13_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r2_hidden(esk4_2(X11,X12),X12)
        | v2_waybel_7(X12,X11)
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,X11)
        | ~ v13_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v3_orders_2(X11)
        | ~ v4_orders_2(X11)
        | ~ v5_orders_2(X11)
        | ~ v1_lattice3(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_waybel_7])])])])])])).

fof(c_0_17,plain,(
    ! [X36,X37] :
      ( ( v2_waybel_0(X37,k7_lattice3(X36))
        | ~ v1_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k7_lattice3(X36))))
        | ~ v1_waybel_0(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_orders_2(X36) )
      & ( v1_waybel_0(X37,X36)
        | ~ v2_waybel_0(X37,k7_lattice3(X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k7_lattice3(X36))))
        | ~ l1_orders_2(X36) )
      & ( m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_waybel_0(X37,k7_lattice3(X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k7_lattice3(X36))))
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_7])])])])).

fof(c_0_18,plain,(
    ! [X21] :
      ( ( v1_orders_2(k7_lattice3(X21))
        | ~ l1_orders_2(X21) )
      & ( l1_orders_2(k7_lattice3(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

fof(c_0_19,negated_conjecture,
    ( v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_lattice3(esk5_0)
    & v2_lattice3(esk5_0)
    & l1_orders_2(esk5_0)
    & ( v1_xboole_0(esk6_0)
      | ~ v1_waybel_0(esk6_0,esk5_0)
      | ~ v12_waybel_0(esk6_0,esk5_0)
      | ~ v1_waybel_7(esk6_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      | v1_xboole_0(esk6_0)
      | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | ~ v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0)))) )
    & ( ~ v1_xboole_0(esk6_0)
      | ~ v1_xboole_0(esk6_0) )
    & ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | ~ v1_xboole_0(esk6_0) )
    & ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | ~ v1_xboole_0(esk6_0) )
    & ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
      | ~ v1_xboole_0(esk6_0) )
    & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
      | ~ v1_xboole_0(esk6_0) )
    & ( ~ v1_xboole_0(esk6_0)
      | v1_waybel_0(esk6_0,esk5_0) )
    & ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | v1_waybel_0(esk6_0,esk5_0) )
    & ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | v1_waybel_0(esk6_0,esk5_0) )
    & ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
      | v1_waybel_0(esk6_0,esk5_0) )
    & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
      | v1_waybel_0(esk6_0,esk5_0) )
    & ( ~ v1_xboole_0(esk6_0)
      | v12_waybel_0(esk6_0,esk5_0) )
    & ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | v12_waybel_0(esk6_0,esk5_0) )
    & ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | v12_waybel_0(esk6_0,esk5_0) )
    & ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
      | v12_waybel_0(esk6_0,esk5_0) )
    & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
      | v12_waybel_0(esk6_0,esk5_0) )
    & ( ~ v1_xboole_0(esk6_0)
      | v1_waybel_7(esk6_0,esk5_0) )
    & ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | v1_waybel_7(esk6_0,esk5_0) )
    & ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | v1_waybel_7(esk6_0,esk5_0) )
    & ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
      | v1_waybel_7(esk6_0,esk5_0) )
    & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
      | v1_waybel_7(esk6_0,esk5_0) )
    & ( ~ v1_xboole_0(esk6_0)
      | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) )
    & ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) )
    & ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
      | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) )
    & ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
      | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) )
    & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
      | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ v1_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v2_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
    | v1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | v1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( r2_hidden(k13_lattice3(X1,esk3_2(X1,X2),esk4_2(X1,X2)),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | m1_subset_1(esk3_2(k7_lattice3(X2),X1),u1_struct_0(k7_lattice3(X2)))
    | v1_xboole_0(X1)
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_waybel_0(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26])]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X29] :
      ( ( v1_orders_2(k7_lattice3(X29))
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) )
      & ( v1_lattice3(k7_lattice3(X29))
        | ~ v2_lattice3(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_yellow_7])])])).

cnf(c_0_39,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | m1_subset_1(esk4_2(k7_lattice3(X2),X1),u1_struct_0(k7_lattice3(X2)))
    | v1_xboole_0(X1)
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_40,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | r2_hidden(k13_lattice3(k7_lattice3(X2),esk3_2(k7_lattice3(X2),X1),esk4_2(k7_lattice3(X2),X1)),X1)
    | v1_xboole_0(X1)
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_lattice3(k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_26])]),c_0_37])).

cnf(c_0_42,plain,
    ( v1_lattice3(k7_lattice3(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_44,plain,(
    ! [X28] :
      ( ( v1_orders_2(k7_lattice3(X28))
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( v5_orders_2(k7_lattice3(X28))
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_yellow_7])])])).

cnf(c_0_45,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_lattice3(k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_36]),c_0_26])]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k13_lattice3(k7_lattice3(esk5_0),esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_lattice3(k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_35]),c_0_36]),c_0_26])]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26]),c_0_43])])).

cnf(c_0_48,plain,
    ( v5_orders_2(k7_lattice3(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_50,plain,(
    ! [X27] :
      ( ( v1_orders_2(k7_lattice3(X27))
        | ~ v4_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( v4_orders_2(k7_lattice3(X27))
        | ~ v4_orders_2(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_yellow_7])])])).

cnf(c_0_51,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_26]),c_0_43])])).

fof(c_0_52,plain,(
    ! [X30,X31,X32] :
      ( ~ v3_orders_2(X30)
      | ~ v4_orders_2(X30)
      | ~ v5_orders_2(X30)
      | ~ v2_lattice3(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | k12_lattice3(X30,X31,X32) = k13_lattice3(k7_lattice3(X30),k8_lattice3(X30,X31),k8_lattice3(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_7])])])).

fof(c_0_53,plain,(
    ! [X26] :
      ( ( v1_orders_2(k7_lattice3(X26))
        | ~ v3_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( v3_orders_2(k7_lattice3(X26))
        | ~ v3_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_yellow_7])])])).

fof(c_0_54,plain,(
    ! [X22,X23] :
      ( ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_subset_1(k8_lattice3(X22,X23),u1_struct_0(k7_lattice3(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_lattice3])])).

fof(c_0_55,plain,(
    ! [X38,X39] :
      ( ( v13_waybel_0(X39,k7_lattice3(X38))
        | ~ v12_waybel_0(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_orders_2(X38) )
      & ( m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k7_lattice3(X38))))
        | ~ v12_waybel_0(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_orders_2(X38) )
      & ( v12_waybel_0(X39,X38)
        | ~ v13_waybel_0(X39,k7_lattice3(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k7_lattice3(X38))))
        | ~ l1_orders_2(X38) )
      & ( m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ v13_waybel_0(X39,k7_lattice3(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(k7_lattice3(X38))))
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_yellow_7])])])])).

cnf(c_0_56,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k13_lattice3(k7_lattice3(esk5_0),esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_42]),c_0_26]),c_0_43])])).

cnf(c_0_57,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26]),c_0_49])])).

cnf(c_0_58,plain,
    ( v4_orders_2(k7_lattice3(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_26]),c_0_49])])).

cnf(c_0_61,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,plain,
    ( k12_lattice3(X1,X2,X3) = k13_lattice3(k7_lattice3(X1),k8_lattice3(X1,X2),k8_lattice3(X1,X3))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( v3_orders_2(k7_lattice3(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( m1_subset_1(k8_lattice3(X1,X2),u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_65,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v1_waybel_7(X6,X5)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(k12_lattice3(X5,X7,X8),X6)
        | r2_hidden(X7,X6)
        | r2_hidden(X8,X6)
        | v1_xboole_0(X6)
        | ~ v1_waybel_0(X6,X5)
        | ~ v12_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | v1_waybel_7(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_waybel_0(X6,X5)
        | ~ v12_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk2_2(X5,X6),u1_struct_0(X5))
        | v1_waybel_7(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_waybel_0(X6,X5)
        | ~ v12_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(k12_lattice3(X5,esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | v1_waybel_7(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_waybel_0(X6,X5)
        | ~ v12_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r2_hidden(esk1_2(X5,X6),X6)
        | v1_waybel_7(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_waybel_0(X6,X5)
        | ~ v12_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r2_hidden(esk2_2(X5,X6),X6)
        | v1_waybel_7(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_waybel_0(X6,X5)
        | ~ v12_waybel_0(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_waybel_7])])])])])])).

cnf(c_0_66,plain,
    ( v12_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
    | v12_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | v12_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k13_lattice3(k7_lattice3(esk5_0),esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_26]),c_0_49])])).

fof(c_0_70,plain,(
    ! [X17,X18] :
      ( ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | k8_lattice3(X17,X18) = X18 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_lattice3])])])).

fof(c_0_71,plain,(
    ! [X24,X25] :
      ( ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,u1_struct_0(k7_lattice3(X24)))
      | m1_subset_1(k9_lattice3(X24,X25),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_lattice3])])).

fof(c_0_72,plain,(
    ! [X19,X20] :
      ( ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(k7_lattice3(X19)))
      | k9_lattice3(X19,X20) = X20 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_lattice3])])])).

cnf(c_0_73,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26]),c_0_59])])).

cnf(c_0_74,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_26]),c_0_59])])).

cnf(c_0_76,plain,
    ( r2_hidden(k8_lattice3(X1,X2),X3)
    | r2_hidden(k8_lattice3(X1,X4),X3)
    | v1_xboole_0(X3)
    | ~ v2_waybel_7(X3,k7_lattice3(X1))
    | ~ v13_waybel_0(X3,k7_lattice3(X1))
    | ~ v2_waybel_0(X3,k7_lattice3(X1))
    | ~ r2_hidden(k12_lattice3(X1,X2,X4),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_58]),c_0_48]),c_0_22]),c_0_64]),c_0_64]),c_0_42])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_80,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_81,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_82,negated_conjecture,
    ( v12_waybel_0(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_26])]),c_0_68])).

cnf(c_0_83,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_84,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k13_lattice3(k7_lattice3(esk5_0),esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_26]),c_0_59])])).

cnf(c_0_86,plain,
    ( k8_lattice3(X1,X2) = X2
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_87,plain,
    ( m1_subset_1(k9_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_88,plain,
    ( k9_lattice3(X1,X2) = X2
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_89,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_63]),c_0_26]),c_0_74])])).

cnf(c_0_90,plain,
    ( v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_91,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0)))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_63]),c_0_26]),c_0_74])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k8_lattice3(esk5_0,X1),esk6_0)
    | r2_hidden(k8_lattice3(esk5_0,X2),esk6_0)
    | v1_waybel_7(esk6_0,esk5_0)
    | ~ r2_hidden(k12_lattice3(esk5_0,X2,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37]),c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk5_0,esk1_2(esk5_0,esk6_0),esk2_2(esk5_0,esk6_0)),esk6_0)
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_35]),c_0_82]),c_0_36]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37])).

cnf(c_0_94,negated_conjecture,
    ( v1_waybel_7(esk6_0,esk5_0)
    | m1_subset_1(esk1_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_35]),c_0_82]),c_0_36]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37])).

cnf(c_0_95,negated_conjecture,
    ( v1_waybel_7(esk6_0,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_35]),c_0_82]),c_0_36]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37])).

cnf(c_0_96,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_97,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k13_lattice3(k7_lattice3(esk5_0),esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_63]),c_0_26]),c_0_74])])).

cnf(c_0_98,plain,
    ( k13_lattice3(k7_lattice3(X1),k8_lattice3(X1,X2),X3) = k12_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_86])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X2)))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_35]),c_0_82]),c_0_26])])).

cnf(c_0_101,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(k7_lattice3(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_90]),c_0_35]),c_0_82]),c_0_26])])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k8_lattice3(esk5_0,esk1_2(esk5_0,esk6_0)),esk6_0)
    | r2_hidden(k8_lattice3(esk5_0,esk2_2(esk5_0,esk6_0)),esk6_0)
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( v1_waybel_7(esk6_0,esk5_0)
    | ~ r2_hidden(esk2_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_35]),c_0_82]),c_0_36]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37])).

cnf(c_0_104,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_105,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k13_lattice3(k7_lattice3(esk5_0),esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_90]),c_0_35]),c_0_82]),c_0_26])])).

cnf(c_0_106,plain,
    ( k13_lattice3(k7_lattice3(X1),X2,X3) = k12_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_86])).

cnf(c_0_107,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk3_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_26])])).

cnf(c_0_108,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | m1_subset_1(esk4_2(k7_lattice3(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_101]),c_0_26])])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k8_lattice3(esk5_0,esk1_2(esk5_0,esk6_0)),esk6_0)
    | v1_waybel_7(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_86]),c_0_26])]),c_0_95]),c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( v1_waybel_7(esk6_0,esk5_0)
    | ~ r2_hidden(esk1_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_35]),c_0_82]),c_0_36]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37])).

cnf(c_0_111,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_112,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_113,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(k12_lattice3(esk5_0,esk3_2(k7_lattice3(esk5_0),esk6_0),esk4_2(k7_lattice3(esk5_0),esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_107]),c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( v1_waybel_7(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_86]),c_0_26])]),c_0_94]),c_0_110])).

cnf(c_0_115,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ r2_hidden(esk4_2(k7_lattice3(X2),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_116,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0)
    | r2_hidden(esk4_2(k7_lattice3(esk5_0),esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_35]),c_0_82]),c_0_36]),c_0_26]),c_0_43]),c_0_49]),c_0_59]),c_0_74])]),c_0_37]),c_0_107]),c_0_108])).

cnf(c_0_117,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_lattice3(k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_35]),c_0_36]),c_0_26])]),c_0_37])).

cnf(c_0_118,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_42]),c_0_26]),c_0_43])])).

cnf(c_0_119,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_48]),c_0_26]),c_0_49])])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(esk6_0)
    | ~ v1_waybel_0(esk6_0,esk5_0)
    | ~ v12_waybel_0(esk6_0,esk5_0)
    | ~ v1_waybel_7(esk6_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_121,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_58]),c_0_26]),c_0_59])])).

cnf(c_0_122,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_waybel_0(esk6_0,esk5_0)
    | ~ v12_waybel_0(esk6_0,esk5_0)
    | ~ v1_waybel_7(esk6_0,esk5_0)
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0)))) ),
    inference(cn,[status(thm)],[c_0_120])).

cnf(c_0_123,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_124,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0)
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_63]),c_0_26]),c_0_74])])).

cnf(c_0_125,negated_conjecture,
    ( ~ v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_waybel_7(esk6_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v12_waybel_0(esk6_0,esk5_0)
    | ~ v1_waybel_0(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_122,c_0_37])).

cnf(c_0_126,plain,
    ( v2_waybel_7(X1,k7_lattice3(X2))
    | v1_xboole_0(X1)
    | ~ v13_waybel_0(X1,k7_lattice3(X2))
    | ~ v1_lattice3(k7_lattice3(X2))
    | ~ r2_hidden(esk3_2(k7_lattice3(X2),X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(k7_lattice3(X2))
    | ~ v4_orders_2(k7_lattice3(X2))
    | ~ v3_orders_2(k7_lattice3(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_127,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | r2_hidden(esk3_2(k7_lattice3(esk5_0),esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_90]),c_0_35]),c_0_82]),c_0_26])])).

cnf(c_0_128,negated_conjecture,
    ( ~ v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_waybel_7(esk6_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_35]),c_0_82]),c_0_36])])).

cnf(c_0_129,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v1_lattice3(k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_35]),c_0_36]),c_0_26])]),c_0_37])).

cnf(c_0_130,negated_conjecture,
    ( ~ v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_114])])).

cnf(c_0_131,negated_conjecture,
    ( v2_waybel_7(esk6_0,k7_lattice3(esk5_0))
    | ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_42]),c_0_26]),c_0_43])])).

cnf(c_0_132,negated_conjecture,
    ( ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k7_lattice3(esk5_0))))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( ~ v13_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_21]),c_0_35]),c_0_36]),c_0_26])])).

cnf(c_0_134,negated_conjecture,
    ( ~ v2_waybel_0(esk6_0,k7_lattice3(esk5_0))
    | ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_90]),c_0_35]),c_0_82]),c_0_26])])).

cnf(c_0_135,negated_conjecture,
    ( ~ v5_orders_2(k7_lattice3(esk5_0))
    | ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_23]),c_0_35]),c_0_36]),c_0_26])])).

cnf(c_0_136,negated_conjecture,
    ( ~ v4_orders_2(k7_lattice3(esk5_0))
    | ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_48]),c_0_26]),c_0_49])])).

cnf(c_0_137,negated_conjecture,
    ( ~ v3_orders_2(k7_lattice3(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_58]),c_0_26]),c_0_59])])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_63]),c_0_26]),c_0_74])]),
    [proof]).

%------------------------------------------------------------------------------
