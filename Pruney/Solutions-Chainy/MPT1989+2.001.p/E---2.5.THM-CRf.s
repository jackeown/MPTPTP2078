%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:31 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 525 expanded)
%              Number of clauses        :   61 ( 179 expanded)
%              Number of leaves         :   14 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  519 (3534 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v4_waybel_7(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(d6_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v4_waybel_7(X2,X1)
          <=> ? [X3] :
                ( ~ v1_xboole_0(X3)
                & v1_waybel_0(X3,X1)
                & v12_waybel_0(X3,X1)
                & v1_waybel_7(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                & X2 = k1_yellow_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t37_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v5_waybel_6(X2,X1)
           => v1_waybel_7(k5_waybel_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

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

fof(fc8_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k5_waybel_0(X1,X2))
        & v1_waybel_0(k5_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(fc12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v12_waybel_0(k5_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v5_waybel_6(X2,X1)
             => v4_waybel_7(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_waybel_7])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | m1_subset_1(k5_waybel_0(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

fof(c_0_16,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & v5_waybel_6(esk5_0,esk4_0)
    & ~ v4_waybel_7(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | ~ v1_lattice3(X14)
      | ~ v2_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ v3_orders_2(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | r3_orders_2(X11,X12,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r3_orders_2(X8,X9,X10)
        | r1_orders_2(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ l1_orders_2(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) )
      & ( ~ r1_orders_2(X8,X9,X10)
        | r3_orders_2(X8,X9,X10)
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ l1_orders_2(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r2_hidden(X36,k5_waybel_0(X34,X35))
        | r1_orders_2(X34,X36,X35)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) )
      & ( ~ r1_orders_2(X34,X36,X35)
        | r2_hidden(X36,k5_waybel_0(X34,X35))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_20])])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X16)
        | r1_orders_2(X15,X18,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),u1_struct_0(X15))
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,esk1_3(X15,X16,X17),X17)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,X1)
    | v2_struct_0(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_20]),c_0_28])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k5_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X37,X38,X40] :
      ( ( ~ v1_xboole_0(esk3_2(X37,X38))
        | ~ v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) )
      & ( v1_waybel_0(esk3_2(X37,X38),X37)
        | ~ v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) )
      & ( v12_waybel_0(esk3_2(X37,X38),X37)
        | ~ v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) )
      & ( v1_waybel_7(esk3_2(X37,X38),X37)
        | ~ v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk3_2(X37,X38),k1_zfmisc_1(u1_struct_0(X37)))
        | ~ v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) )
      & ( X38 = k1_yellow_0(X37,esk3_2(X37,X38))
        | ~ v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) )
      & ( v1_xboole_0(X40)
        | ~ v1_waybel_0(X40,X37)
        | ~ v12_waybel_0(X40,X37)
        | ~ v1_waybel_7(X40,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X37)))
        | X38 != k1_yellow_0(X37,X40)
        | v4_waybel_7(X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).

fof(c_0_40,plain,(
    ! [X20,X21] :
      ( ~ l1_orders_2(X20)
      | m1_subset_1(k1_yellow_0(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_41,plain,(
    ! [X41,X42] :
      ( ~ v3_orders_2(X41)
      | ~ v4_orders_2(X41)
      | ~ v5_orders_2(X41)
      | ~ v1_lattice3(X41)
      | ~ v2_lattice3(X41)
      | ~ l1_orders_2(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ v5_waybel_6(X42,X41)
      | v1_waybel_7(k5_waybel_0(X41,X42),X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk5_0)
    | v2_struct_0(esk4_0)
    | ~ r3_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_20]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_19])).

fof(c_0_45,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( r2_lattice3(X22,X24,X23)
        | X23 != k1_yellow_0(X22,X24)
        | ~ r1_yellow_0(X22,X24)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_lattice3(X22,X24,X25)
        | r1_orders_2(X22,X23,X25)
        | X23 != k1_yellow_0(X22,X24)
        | ~ r1_yellow_0(X22,X24)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X23 = k1_yellow_0(X22,X26)
        | m1_subset_1(esk2_3(X22,X23,X26),u1_struct_0(X22))
        | ~ r2_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_yellow_0(X22,X26)
        | m1_subset_1(esk2_3(X22,X23,X26),u1_struct_0(X22))
        | ~ r2_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X23 = k1_yellow_0(X22,X26)
        | r2_lattice3(X22,X26,esk2_3(X22,X23,X26))
        | ~ r2_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_yellow_0(X22,X26)
        | r2_lattice3(X22,X26,esk2_3(X22,X23,X26))
        | ~ r2_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X23 = k1_yellow_0(X22,X26)
        | ~ r1_orders_2(X22,X23,esk2_3(X22,X23,X26))
        | ~ r2_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_yellow_0(X22,X26)
        | ~ r1_orders_2(X22,X23,esk2_3(X22,X23,X26))
        | ~ r2_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk5_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_19]),c_0_20])]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_20])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | v4_waybel_7(X3,X2)
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ v1_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != k1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v1_waybel_7(k5_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_waybel_6(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( v5_waybel_6(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_56,plain,(
    ! [X32,X33] :
      ( ( ~ v1_xboole_0(k5_waybel_0(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32)) )
      & ( v1_waybel_0(k5_waybel_0(X32,X33),X32)
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).

fof(c_0_57,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v4_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | v12_waybel_0(k5_waybel_0(X30,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_20])])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_19])])).

cnf(c_0_61,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_63,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_64,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_65,plain,
    ( v4_waybel_7(k1_yellow_0(X1,X2),X1)
    | v1_xboole_0(X2)
    | ~ v1_waybel_7(X2,X1)
    | ~ v2_lattice3(X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( v1_waybel_7(k5_waybel_0(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_52]),c_0_53]),c_0_54]),c_0_55]),c_0_25]),c_0_20]),c_0_28])])).

cnf(c_0_67,plain,
    ( v1_waybel_0(k5_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v12_waybel_0(k5_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_19]),c_0_20])])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(esk5_0,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_19])])).

cnf(c_0_71,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_19]),c_0_55]),c_0_20])])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_62]),c_0_25]),c_0_20])])).

cnf(c_0_73,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_19]),c_0_55]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( k1_yellow_0(esk4_0,X1) = esk5_0
    | ~ r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_19]),c_0_55]),c_0_20])])).

cnf(c_0_75,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | ~ v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | ~ v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_31]),c_0_66]),c_0_53]),c_0_54]),c_0_55]),c_0_25]),c_0_20]),c_0_28])])).

cnf(c_0_76,negated_conjecture,
    ( v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_19]),c_0_20]),c_0_28])])).

cnf(c_0_77,negated_conjecture,
    ( v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_19]),c_0_54]),c_0_20])])).

cnf(c_0_78,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | v2_struct_0(esk4_0)
    | ~ r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_72])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_83,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0
    | v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_20]),c_0_28]),c_0_19])])).

cnf(c_0_86,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_84]),c_0_25]),c_0_20])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v4_waybel_7(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,negated_conjecture,
    ( v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_88]),c_0_25]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:23:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.40  # and selection function SelectNewComplexAHP.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.037 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t38_waybel_7, conjecture, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_7)).
% 0.19/0.40  fof(dt_k5_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 0.19/0.40  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.19/0.40  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.19/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.40  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.40  fof(t17_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k5_waybel_0(X1,X2))<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_waybel_0)).
% 0.19/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.19/0.40  fof(d6_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)<=>?[X3]:(((((~(v1_xboole_0(X3))&v1_waybel_0(X3,X1))&v12_waybel_0(X3,X1))&v1_waybel_7(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))&X2=k1_yellow_0(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_7)).
% 0.19/0.40  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.40  fof(t37_waybel_7, axiom, ![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v1_waybel_7(k5_waybel_0(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_waybel_7)).
% 0.19/0.40  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.19/0.40  fof(fc8_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>(~(v1_xboole_0(k5_waybel_0(X1,X2)))&v1_waybel_0(k5_waybel_0(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_waybel_0)).
% 0.19/0.40  fof(fc12_waybel_0, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>v12_waybel_0(k5_waybel_0(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_waybel_0)).
% 0.19/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v5_waybel_6(X2,X1)=>v4_waybel_7(X2,X1))))), inference(assume_negation,[status(cth)],[t38_waybel_7])).
% 0.19/0.40  fof(c_0_15, plain, ![X28, X29]:(v2_struct_0(X28)|~l1_orders_2(X28)|~m1_subset_1(X29,u1_struct_0(X28))|m1_subset_1(k5_waybel_0(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).
% 0.19/0.40  fof(c_0_16, negated_conjecture, ((((((v3_orders_2(esk4_0)&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(v5_waybel_6(esk5_0,esk4_0)&~v4_waybel_7(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.40  fof(c_0_17, plain, ![X14]:(~l1_orders_2(X14)|(~v1_lattice3(X14)|~v2_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.19/0.40  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_21, plain, ![X11, X12, X13]:(v2_struct_0(X11)|~v3_orders_2(X11)|~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))|r3_orders_2(X11,X12,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.19/0.40  fof(c_0_22, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|m1_subset_1(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.40  cnf(c_0_23, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (v2_struct_0(esk4_0)|m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_26, plain, ![X8, X9, X10]:((~r3_orders_2(X8,X9,X10)|r1_orders_2(X8,X9,X10)|(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))&(~r1_orders_2(X8,X9,X10)|r3_orders_2(X8,X9,X10)|(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.40  cnf(c_0_27, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_29, plain, ![X34, X35, X36]:((~r2_hidden(X36,k5_waybel_0(X34,X35))|r1_orders_2(X34,X36,X35)|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34)))&(~r1_orders_2(X34,X36,X35)|r2_hidden(X36,k5_waybel_0(X34,X35))|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).
% 0.19/0.40  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(k5_waybel_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_20])])).
% 0.19/0.40  fof(c_0_32, plain, ![X15, X16, X17, X18]:((~r2_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X18,X17)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk1_3(X15,X16,X17),u1_struct_0(X15))|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk1_3(X15,X16,X17),X16)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,esk1_3(X15,X16,X17),X17)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.19/0.40  cnf(c_0_33, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (r3_orders_2(esk4_0,X1,X1)|v2_struct_0(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_19]), c_0_20]), c_0_28])])).
% 0.19/0.40  cnf(c_0_35, plain, (r1_orders_2(X2,X1,X3)|v2_struct_0(X2)|~r2_hidden(X1,k5_waybel_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.40  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_38, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  fof(c_0_39, plain, ![X37, X38, X40]:(((((((~v1_xboole_0(esk3_2(X37,X38))|~v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37)))&(v1_waybel_0(esk3_2(X37,X38),X37)|~v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37))))&(v12_waybel_0(esk3_2(X37,X38),X37)|~v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37))))&(v1_waybel_7(esk3_2(X37,X38),X37)|~v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37))))&(m1_subset_1(esk3_2(X37,X38),k1_zfmisc_1(u1_struct_0(X37)))|~v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37))))&(X38=k1_yellow_0(X37,esk3_2(X37,X38))|~v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37))))&(v1_xboole_0(X40)|~v1_waybel_0(X40,X37)|~v12_waybel_0(X40,X37)|~v1_waybel_7(X40,X37)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X37)))|X38!=k1_yellow_0(X37,X40)|v4_waybel_7(X38,X37)|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~v1_lattice3(X37)|~v2_lattice3(X37)|~l1_orders_2(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_waybel_7])])])])])])).
% 0.19/0.40  fof(c_0_40, plain, ![X20, X21]:(~l1_orders_2(X20)|m1_subset_1(k1_yellow_0(X20,X21),u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.40  fof(c_0_41, plain, ![X41, X42]:(~v3_orders_2(X41)|~v4_orders_2(X41)|~v5_orders_2(X41)|~v1_lattice3(X41)|~v2_lattice3(X41)|~l1_orders_2(X41)|(~m1_subset_1(X42,u1_struct_0(X41))|(~v5_waybel_6(X42,X41)|v1_waybel_7(k5_waybel_0(X41,X42),X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_waybel_7])])])).
% 0.19/0.40  cnf(c_0_42, plain, (r2_hidden(X2,k5_waybel_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk4_0,X1,esk5_0)|v2_struct_0(esk4_0)|~r3_orders_2(esk4_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_19]), c_0_20]), c_0_28])])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (r3_orders_2(esk4_0,esk5_0,esk5_0)|v2_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 0.19/0.40  fof(c_0_45, plain, ![X22, X23, X24, X25, X26]:(((r2_lattice3(X22,X24,X23)|(X23!=k1_yellow_0(X22,X24)|~r1_yellow_0(X22,X24))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22)))&(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_lattice3(X22,X24,X25)|r1_orders_2(X22,X23,X25))|(X23!=k1_yellow_0(X22,X24)|~r1_yellow_0(X22,X24))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22))))&(((X23=k1_yellow_0(X22,X26)|(m1_subset_1(esk2_3(X22,X23,X26),u1_struct_0(X22))|~r2_lattice3(X22,X26,X23))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22)))&(r1_yellow_0(X22,X26)|(m1_subset_1(esk2_3(X22,X23,X26),u1_struct_0(X22))|~r2_lattice3(X22,X26,X23))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22))))&(((X23=k1_yellow_0(X22,X26)|(r2_lattice3(X22,X26,esk2_3(X22,X23,X26))|~r2_lattice3(X22,X26,X23))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22)))&(r1_yellow_0(X22,X26)|(r2_lattice3(X22,X26,esk2_3(X22,X23,X26))|~r2_lattice3(X22,X26,X23))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22))))&((X23=k1_yellow_0(X22,X26)|(~r1_orders_2(X22,X23,esk2_3(X22,X23,X26))|~r2_lattice3(X22,X26,X23))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22)))&(r1_yellow_0(X22,X26)|(~r1_orders_2(X22,X23,esk2_3(X22,X23,X26))|~r2_lattice3(X22,X26,X23))|~m1_subset_1(X23,u1_struct_0(X22))|(~v5_orders_2(X22)|~l1_orders_2(X22))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk4_0,X1,esk5_0)|v2_struct_0(esk4_0)|~r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_19]), c_0_20])]), c_0_36])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk1_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk1_3(esk4_0,X1,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_49, plain, (v1_xboole_0(X1)|v4_waybel_7(X3,X2)|~v1_waybel_0(X1,X2)|~v12_waybel_0(X1,X2)|~v1_waybel_7(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X3!=k1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_lattice3(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.40  cnf(c_0_50, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_51, plain, (v1_waybel_7(k5_waybel_0(X1,X2),X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_waybel_6(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (v5_waybel_6(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (v2_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_56, plain, ![X32, X33]:((~v1_xboole_0(k5_waybel_0(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,u1_struct_0(X32))))&(v1_waybel_0(k5_waybel_0(X32,X33),X32)|(v2_struct_0(X32)|~v3_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,u1_struct_0(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_waybel_0])])])])).
% 0.19/0.40  fof(c_0_57, plain, ![X30, X31]:(v2_struct_0(X30)|~v4_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,u1_struct_0(X30))|v12_waybel_0(k5_waybel_0(X30,X31),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_waybel_0])])])).
% 0.19/0.40  cnf(c_0_58, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (v2_struct_0(esk4_0)|r2_hidden(X1,k5_waybel_0(esk4_0,esk5_0))|~r1_orders_2(esk4_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk5_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_19])])).
% 0.19/0.40  cnf(c_0_61, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.19/0.40  cnf(c_0_63, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_64, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_65, plain, (v4_waybel_7(k1_yellow_0(X1,X2),X1)|v1_xboole_0(X2)|~v1_waybel_7(X2,X1)|~v2_lattice3(X1)|~v1_waybel_0(X2,X1)|~v12_waybel_0(X2,X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_50])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (v1_waybel_7(k5_waybel_0(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_52]), c_0_53]), c_0_54]), c_0_55]), c_0_25]), c_0_20]), c_0_28])])).
% 0.19/0.40  cnf(c_0_67, plain, (v1_waybel_0(k5_waybel_0(X1,X2),X1)|v2_struct_0(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.40  cnf(c_0_68, plain, (v2_struct_0(X1)|v12_waybel_0(k5_waybel_0(X1,X2),X1)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk5_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_19]), c_0_20])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (v2_struct_0(esk4_0)|r2_hidden(esk5_0,k5_waybel_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_19])])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_19]), c_0_55]), c_0_20])])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_62]), c_0_25]), c_0_20])])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|r2_lattice3(esk4_0,X1,esk2_3(esk4_0,esk5_0,X1))|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_19]), c_0_55]), c_0_20])])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k1_yellow_0(esk4_0,X1)=esk5_0|~r2_lattice3(esk4_0,X1,esk5_0)|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_19]), c_0_55]), c_0_20])])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|~v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|~v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_31]), c_0_66]), c_0_53]), c_0_54]), c_0_55]), c_0_25]), c_0_20]), c_0_28])])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (v1_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_19]), c_0_20]), c_0_28])])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (v12_waybel_0(k5_waybel_0(esk4_0,esk5_0),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_19]), c_0_54]), c_0_20])])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|v2_struct_0(esk4_0)|~r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|m1_subset_1(esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|r2_lattice3(esk4_0,k5_waybel_0(esk4_0,esk5_0),esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_73, c_0_72])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|~r1_orders_2(esk4_0,esk5_0,esk2_3(esk4_0,esk5_0,k5_waybel_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_74, c_0_72])).
% 0.19/0.40  cnf(c_0_82, plain, (v2_struct_0(X1)|~v1_xboole_0(k5_waybel_0(X1,X2))|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v1_xboole_0(k5_waybel_0(esk4_0,esk5_0))|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0|v2_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (v4_waybel_7(k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0)),esk4_0)|v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_20]), c_0_28]), c_0_19])])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_84]), c_0_25]), c_0_20])])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (~v4_waybel_7(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (v2_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.19/0.40  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_88]), c_0_25]), c_0_20])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 90
% 0.19/0.40  # Proof object clause steps            : 61
% 0.19/0.40  # Proof object formula steps           : 29
% 0.19/0.40  # Proof object conjectures             : 44
% 0.19/0.40  # Proof object clause conjectures      : 41
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 28
% 0.19/0.40  # Proof object initial formulas used   : 14
% 0.19/0.40  # Proof object generating inferences   : 31
% 0.19/0.40  # Proof object simplifying inferences  : 78
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 14
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 41
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 41
% 0.19/0.40  # Processed clauses                    : 266
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 51
% 0.19/0.40  # ...remaining for further processing  : 215
% 0.19/0.40  # Other redundant clauses eliminated   : 3
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 9
% 0.19/0.40  # Backward-rewritten                   : 67
% 0.19/0.40  # Generated clauses                    : 349
% 0.19/0.40  # ...of the previous two non-trivial   : 354
% 0.19/0.40  # Contextual simplify-reflections      : 12
% 0.19/0.40  # Paramodulations                      : 346
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 3
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 95
% 0.19/0.40  #    Positive orientable unit clauses  : 15
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 79
% 0.19/0.40  # Current number of unprocessed clauses: 170
% 0.19/0.40  # ...number of literals in the above   : 609
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 117
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 4435
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1340
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 67
% 0.19/0.40  # Unit Clause-clause subsumption calls : 98
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 9
% 0.19/0.40  # BW rewrite match successes           : 7
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 14709
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.061 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.068 s
% 0.19/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
