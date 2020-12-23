%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t24_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 239.96s
% Output     : CNFRefutation 239.96s
% Verified   : 
% Statistics : Number of formulae       :  146 (14154 expanded)
%              Number of clauses        :  107 (4459 expanded)
%              Number of leaves         :   19 (3523 expanded)
%              Depth                    :   35
%              Number of atoms          :  817 (163855 expanded)
%              Number of equality atoms :   25 ( 563 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   70 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v11_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                  | r2_hidden(k7_waybel_1(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t24_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',cc2_lattice3)).

fof(t22_waybel_4,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => r2_hidden(k4_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t22_waybel_4)).

fof(cc4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_yellow_0(X1)
       => ( v1_yellow_0(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',cc4_yellow_0)).

fof(cc8_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_yellow_0(X1)
          & v2_waybel_1(X1)
          & v10_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',cc8_waybel_1)).

fof(t41_waybel_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(k12_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t41_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',d2_waybel_7)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t7_boole)).

fof(t37_yellow_5,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v11_waybel_1(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k12_lattice3(X1,X2,k7_waybel_1(X1,X2)) = k3_yellow_0(X1)
            & k13_lattice3(X1,X2,k7_waybel_1(X1,X2)) = k4_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t37_yellow_5)).

fof(t39_yellow_5,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v11_waybel_1(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k7_waybel_1(X1,k13_lattice3(X1,X2,X3)) = k12_lattice3(X1,k7_waybel_1(X1,X2),k7_waybel_1(X1,X3))
                & k7_waybel_1(X1,k12_lattice3(X1,X2,X3)) = k13_lattice3(X1,k7_waybel_1(X1,X2),k7_waybel_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t39_yellow_5)).

fof(dt_k7_waybel_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_waybel_1(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',dt_k7_waybel_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t1_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t2_subset)).

fof(dt_k4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',dt_k4_yellow_0)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',t44_yellow_0)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',commutativity_k12_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t24_waybel_7.p',d20_waybel_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v11_waybel_1(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_waybel_7(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( r2_hidden(X3,X2)
                    | r2_hidden(k7_waybel_1(X1,X3),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_7])).

fof(c_0_20,plain,(
    ! [X105] :
      ( ~ l1_orders_2(X105)
      | ~ v2_lattice3(X105)
      | ~ v2_struct_0(X105) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_21,negated_conjecture,(
    ! [X8] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v11_waybel_1(esk1_0)
      & v1_lattice3(esk1_0)
      & v2_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & v2_waybel_0(esk2_0,esk1_0)
      & v13_waybel_0(esk2_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ v2_waybel_7(esk2_0,esk1_0) )
      & ( ~ r2_hidden(esk3_0,esk2_0)
        | ~ v2_waybel_7(esk2_0,esk1_0) )
      & ( ~ r2_hidden(k7_waybel_1(esk1_0,esk3_0),esk2_0)
        | ~ v2_waybel_7(esk2_0,esk1_0) )
      & ( v2_waybel_7(esk2_0,esk1_0)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0))
        | r2_hidden(X8,esk2_0)
        | r2_hidden(k7_waybel_1(esk1_0,X8),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])])])).

fof(c_0_22,plain,(
    ! [X75,X76] :
      ( v2_struct_0(X75)
      | ~ v3_orders_2(X75)
      | ~ v4_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ v2_yellow_0(X75)
      | ~ l1_orders_2(X75)
      | v1_xboole_0(X76)
      | ~ v2_waybel_0(X76,X75)
      | ~ v13_waybel_0(X76,X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
      | r2_hidden(k4_yellow_0(X75),X76) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_waybel_4])])])])).

cnf(c_0_23,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k4_yellow_0(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_35,plain,(
    ! [X106] :
      ( ( v1_yellow_0(X106)
        | ~ v3_yellow_0(X106)
        | ~ l1_orders_2(X106) )
      & ( v2_yellow_0(X106)
        | ~ v3_yellow_0(X106)
        | ~ l1_orders_2(X106) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_yellow_0(esk1_0),esk2_0)
    | ~ v2_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_25]),c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_37,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_38,plain,(
    ! [X107] :
      ( ( ~ v2_struct_0(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v3_orders_2(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v4_orders_2(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v5_orders_2(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v1_lattice3(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v2_lattice3(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v3_yellow_0(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v2_waybel_1(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) )
      & ( v10_waybel_1(X107)
        | v2_struct_0(X107)
        | ~ v11_waybel_1(X107)
        | ~ l1_orders_2(X107) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

fof(c_0_39,plain,(
    ! [X86,X87,X88,X89] :
      ( ( ~ v2_waybel_0(X87,X86)
        | ~ m1_subset_1(X88,u1_struct_0(X86))
        | ~ m1_subset_1(X89,u1_struct_0(X86))
        | ~ r2_hidden(X88,X87)
        | ~ r2_hidden(X89,X87)
        | r2_hidden(k12_lattice3(X86,X88,X89),X87)
        | ~ v13_waybel_0(X87,X86)
        | ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) )
      & ( m1_subset_1(esk11_2(X86,X87),u1_struct_0(X86))
        | v2_waybel_0(X87,X86)
        | ~ v13_waybel_0(X87,X86)
        | ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) )
      & ( m1_subset_1(esk12_2(X86,X87),u1_struct_0(X86))
        | v2_waybel_0(X87,X86)
        | ~ v13_waybel_0(X87,X86)
        | ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) )
      & ( r2_hidden(esk11_2(X86,X87),X87)
        | v2_waybel_0(X87,X86)
        | ~ v13_waybel_0(X87,X86)
        | ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) )
      & ( r2_hidden(esk12_2(X86,X87),X87)
        | v2_waybel_0(X87,X86)
        | ~ v13_waybel_0(X87,X86)
        | ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) )
      & ( ~ r2_hidden(k12_lattice3(X86,esk11_2(X86,X87),esk12_2(X86,X87)),X87)
        | v2_waybel_0(X87,X86)
        | ~ v13_waybel_0(X87,X86)
        | ~ m1_subset_1(X87,k1_zfmisc_1(u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_waybel_0])])])])])).

fof(c_0_40,plain,(
    ! [X94,X95,X96] :
      ( ~ r2_hidden(X94,X95)
      | ~ m1_subset_1(X95,k1_zfmisc_1(X96))
      | m1_subset_1(X94,X96) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_41,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ v2_waybel_7(X24,X23)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_hidden(k13_lattice3(X23,X25,X26),X24)
        | r2_hidden(X25,X24)
        | r2_hidden(X26,X24)
        | v1_xboole_0(X24)
        | ~ v2_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk6_2(X23,X24),u1_struct_0(X23))
        | v2_waybel_7(X24,X23)
        | v1_xboole_0(X24)
        | ~ v2_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk7_2(X23,X24),u1_struct_0(X23))
        | v2_waybel_7(X24,X23)
        | v1_xboole_0(X24)
        | ~ v2_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(k13_lattice3(X23,esk6_2(X23,X24),esk7_2(X23,X24)),X24)
        | v2_waybel_7(X24,X23)
        | v1_xboole_0(X24)
        | ~ v2_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r2_hidden(esk6_2(X23,X24),X24)
        | v2_waybel_7(X24,X23)
        | v1_xboole_0(X24)
        | ~ v2_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r2_hidden(esk7_2(X23,X24),X24)
        | v2_waybel_7(X24,X23)
        | v1_xboole_0(X24)
        | ~ v2_waybel_0(X24,X23)
        | ~ v13_waybel_0(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ v1_lattice3(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_waybel_7])])])])])])).

fof(c_0_42,plain,(
    ! [X101,X102] :
      ( ~ r2_hidden(X101,X102)
      | ~ v1_xboole_0(X102) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_yellow_0(esk1_0),esk2_0)
    | ~ v3_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25])])).

cnf(c_0_44,plain,
    ( v3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v11_waybel_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_46,plain,(
    ! [X79,X80] :
      ( ( k12_lattice3(X79,X80,k7_waybel_1(X79,X80)) = k3_yellow_0(X79)
        | ~ m1_subset_1(X80,u1_struct_0(X79))
        | v2_struct_0(X79)
        | ~ v11_waybel_1(X79)
        | ~ l1_orders_2(X79) )
      & ( k13_lattice3(X79,X80,k7_waybel_1(X79,X80)) = k4_yellow_0(X79)
        | ~ m1_subset_1(X80,u1_struct_0(X79))
        | v2_struct_0(X79)
        | ~ v11_waybel_1(X79)
        | ~ l1_orders_2(X79) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_yellow_5])])])])])).

cnf(c_0_47,plain,
    ( r2_hidden(k12_lattice3(X2,X3,X4),X1)
    | ~ v2_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_yellow_0(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_52,plain,
    ( k13_lattice3(X1,X2,k7_waybel_1(X1,X2)) = k4_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(k12_lattice3(X1,X2,X3),X4)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X4,X1)
    | ~ v2_waybel_0(X4,X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_47,c_0_48]),c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(k13_lattice3(X4,X1,X3),X2)
    | ~ v2_waybel_7(X2,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ v13_waybel_0(X2,X4)
    | ~ v2_waybel_0(X2,X4)
    | ~ l1_orders_2(X4)
    | ~ v1_lattice3(X4)
    | ~ v5_orders_2(X4)
    | ~ v4_orders_2(X4)
    | ~ v3_orders_2(X4) ),
    inference(csr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k13_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1)),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( v2_waybel_7(esk2_0,esk1_0)
    | r2_hidden(X1,esk2_0)
    | r2_hidden(k7_waybel_1(esk1_0,X1),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_27]),c_0_28]),c_0_29]),c_0_25]),c_0_24]),c_0_30])])).

cnf(c_0_59,plain,
    ( k12_lattice3(X1,X2,k7_waybel_1(X1,X2)) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28])).

fof(c_0_61,plain,(
    ! [X81,X82,X83] :
      ( ( k7_waybel_1(X81,k13_lattice3(X81,X82,X83)) = k12_lattice3(X81,k7_waybel_1(X81,X82),k7_waybel_1(X81,X83))
        | ~ m1_subset_1(X83,u1_struct_0(X81))
        | ~ m1_subset_1(X82,u1_struct_0(X81))
        | v2_struct_0(X81)
        | ~ v11_waybel_1(X81)
        | ~ l1_orders_2(X81) )
      & ( k7_waybel_1(X81,k12_lattice3(X81,X82,X83)) = k13_lattice3(X81,k7_waybel_1(X81,X82),k7_waybel_1(X81,X83))
        | ~ m1_subset_1(X83,u1_struct_0(X81))
        | ~ m1_subset_1(X82,u1_struct_0(X81))
        | v2_struct_0(X81)
        | ~ v11_waybel_1(X81)
        | ~ l1_orders_2(X81) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_5])])])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(k7_waybel_1(esk1_0,esk3_0),esk2_0)
    | ~ v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,X1),esk2_0)
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k7_waybel_1(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    | ~ v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0)
    | ~ v2_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_66,plain,(
    ! [X56,X57] :
      ( v2_struct_0(X56)
      | ~ l1_orders_2(X56)
      | ~ m1_subset_1(X57,u1_struct_0(X56))
      | m1_subset_1(k7_waybel_1(X56,X57),u1_struct_0(X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_waybel_1])])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k7_waybel_1(esk1_0,X1),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_25]),c_0_45])]),c_0_33]),c_0_60])).

cnf(c_0_68,plain,
    ( k7_waybel_1(X1,k13_lattice3(X1,X2,X3)) = k12_lattice3(X1,k7_waybel_1(X1,X2),k7_waybel_1(X1,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k7_waybel_1(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_waybel_1(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k12_lattice3(esk1_0,k7_waybel_1(esk1_0,X1),k7_waybel_1(esk1_0,X2)),esk2_0)
    | ~ r2_hidden(k13_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_72,plain,
    ( r2_hidden(k13_lattice3(X1,esk6_2(X1,X2),esk7_2(X1,X2)),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_25])]),c_0_33]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k12_lattice3(esk1_0,k7_waybel_1(esk1_0,esk6_2(esk1_0,esk2_0)),k7_waybel_1(esk1_0,esk7_2(esk1_0,esk2_0))),esk2_0)
    | ~ m1_subset_1(esk7_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73]),c_0_34])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_76,plain,(
    ! [X73,X74] :
      ( ~ r2_hidden(X73,X74)
      | m1_subset_1(X73,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_77,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k7_waybel_1(esk1_0,esk7_2(esk1_0,esk2_0)),esk2_0)
    | ~ r2_hidden(k7_waybel_1(esk1_0,esk6_2(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(esk7_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,esk7_2(esk1_0,X1)),esk2_0)
    | r2_hidden(esk7_2(esk1_0,X1),esk2_0)
    | v2_waybel_7(X1,esk1_0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v13_waybel_0(X1,esk1_0)
    | ~ v2_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_75]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( v2_waybel_7(X1,X2)
    | ~ r2_hidden(esk7_2(X2,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_77,c_0_50])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk7_2(esk1_0,esk2_0),esk2_0)
    | r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k7_waybel_1(esk1_0,esk6_2(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(esk7_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_28]),c_0_29]),c_0_27])]),c_0_73]),c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k4_yellow_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_51])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k7_waybel_1(esk1_0,esk6_2(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(esk7_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73])).

cnf(c_0_85,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k13_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1)),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_52]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_87,plain,
    ( k7_waybel_1(X1,k12_lattice3(X1,X2,X3)) = k13_lattice3(X1,k7_waybel_1(X1,X2),k7_waybel_1(X1,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_88,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ r2_hidden(k7_waybel_1(esk1_0,esk6_2(esk1_0,esk2_0)),esk2_0)
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_75]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73]),c_0_34])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,esk6_2(esk1_0,X1)),esk2_0)
    | r2_hidden(esk6_2(esk1_0,X1),esk2_0)
    | v2_waybel_7(X1,esk1_0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v13_waybel_0(X1,esk1_0)
    | ~ v2_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_85]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k7_waybel_1(esk1_0,k12_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1))),esk2_0)
    | ~ m1_subset_1(k7_waybel_1(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_92,plain,
    ( v2_waybel_7(X1,X2)
    | ~ r2_hidden(esk6_2(X2,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2)
    | ~ l1_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_88,c_0_50])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,esk2_0),esk2_0)
    | r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_28]),c_0_29]),c_0_27])]),c_0_73]),c_0_34])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)),esk2_0)
    | ~ m1_subset_1(k7_waybel_1(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_59]),c_0_25]),c_0_45])]),c_0_33])).

fof(c_0_95,plain,(
    ! [X61] : m1_subset_1(esk10_1(X61),X61) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0)
    | ~ m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73])).

fof(c_0_97,plain,(
    ! [X77,X78] :
      ( ~ m1_subset_1(X77,X78)
      | v1_xboole_0(X78)
      | r2_hidden(X77,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_70]),c_0_25])]),c_0_33])).

cnf(c_0_99,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_85]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73]),c_0_34])).

cnf(c_0_101,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1)),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_59]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_104,plain,
    ( k7_waybel_1(X1,k4_yellow_0(X1)) = k12_lattice3(X1,k7_waybel_1(X1,X2),k7_waybel_1(X1,k7_waybel_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v11_waybel_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_52]),c_0_70])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_34])).

cnf(c_0_106,plain,
    ( k7_waybel_1(X1,k12_lattice3(X1,X2,k7_waybel_1(X1,X2))) = k4_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v11_waybel_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_87]),c_0_70])).

cnf(c_0_107,plain,
    ( r2_hidden(esk10_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,k4_yellow_0(esk1_0)),esk2_0)
    | ~ m1_subset_1(k7_waybel_1(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_100])).

cnf(c_0_111,plain,
    ( k4_yellow_0(X1) = k7_waybel_1(X1,k3_yellow_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v11_waybel_1(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_59])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk10_1(esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_107]),c_0_34])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,k4_yellow_0(esk1_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])])).

cnf(c_0_114,negated_conjecture,
    ( k4_yellow_0(esk1_0) = k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_25]),c_0_45])]),c_0_33])).

fof(c_0_115,plain,(
    ! [X50] :
      ( ~ l1_orders_2(X50)
      | m1_subset_1(k4_yellow_0(X50),u1_struct_0(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k12_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1)))),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_106]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_117,negated_conjecture,
    ( k7_waybel_1(esk1_0,k12_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1))) = k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_114]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_118,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_119,plain,
    ( k4_yellow_0(X1) = k7_waybel_1(X1,k3_yellow_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v11_waybel_1(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_99])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_59]),c_0_25]),c_0_45])]),c_0_33])).

fof(c_0_121,plain,(
    ! [X92,X93] :
      ( v2_struct_0(X92)
      | ~ v5_orders_2(X92)
      | ~ v1_yellow_0(X92)
      | ~ l1_orders_2(X92)
      | ~ m1_subset_1(X93,u1_struct_0(X92))
      | r1_orders_2(X92,k3_yellow_0(X92),X93) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_122,negated_conjecture,
    ( k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)))) = k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))
    | ~ m1_subset_1(k7_waybel_1(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_104]),c_0_114]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_123,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_waybel_1(X1,k3_yellow_0(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v11_waybel_1(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_99])).

cnf(c_0_125,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_126,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_127,plain,(
    ! [X11,X12,X13] :
      ( ~ v5_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k12_lattice3(X11,X12,X13) = k12_lattice3(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

cnf(c_0_128,negated_conjecture,
    ( k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)))) = k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_110]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_124])).

cnf(c_0_130,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v3_yellow_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_131,plain,
    ( v5_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_132,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( k12_lattice3(esk1_0,k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))),k7_waybel_1(esk1_0,k3_yellow_0(esk1_0))) = k3_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_128]),c_0_129]),c_0_25]),c_0_45])]),c_0_33])).

fof(c_0_134,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X19,X18)
        | ~ r1_orders_2(X17,X19,X20)
        | r2_hidden(X20,X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk4_2(X17,X18),u1_struct_0(X17))
        | v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_2(X17,X18),u1_struct_0(X17))
        | v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X18)
        | v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk4_2(X17,X18),esk5_2(X17,X18))
        | v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( ~ r2_hidden(esk5_2(X17,X18),X18)
        | v13_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

cnf(c_0_135,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k12_lattice3(X1,X2,k7_waybel_1(X1,X2)),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v11_waybel_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_59]),c_0_131]),c_0_44])).

cnf(c_0_136,negated_conjecture,
    ( k12_lattice3(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)),k7_waybel_1(esk1_0,k7_waybel_1(esk1_0,k3_yellow_0(esk1_0)))) = k3_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_109]),c_0_129]),c_0_25]),c_0_24]),c_0_30])])).

cnf(c_0_137,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( r1_orders_2(esk1_0,k3_yellow_0(esk1_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_109]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_139,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v13_waybel_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_137,c_0_48])).

cnf(c_0_140,negated_conjecture,
    ( r1_orders_2(esk1_0,k12_lattice3(esk1_0,X1,k7_waybel_1(esk1_0,X1)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_59]),c_0_25]),c_0_45])]),c_0_33])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k12_lattice3(esk1_0,X3,k7_waybel_1(esk1_0,X3)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ v13_waybel_0(X2,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_25])])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_103]),c_0_28]),c_0_29])])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_99])).

cnf(c_0_144,negated_conjecture,
    ( v2_waybel_7(esk2_0,X1)
    | ~ m1_subset_1(esk7_2(X1,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(esk2_0,X1)
    | ~ v2_waybel_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_143])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_75]),c_0_28]),c_0_29]),c_0_27]),c_0_25]),c_0_56]),c_0_30]),c_0_31]),c_0_32])]),c_0_73]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
