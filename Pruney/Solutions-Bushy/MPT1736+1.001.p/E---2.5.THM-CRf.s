%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1736+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:40 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 728 expanded)
%              Number of clauses        :   53 ( 229 expanded)
%              Number of leaves         :   12 ( 176 expanded)
%              Depth                    :   12
%              Number of atoms          :  549 (8222 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_borsuk_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ( ( m1_pre_topc(X2,X4)
                      & r1_tsep_1(X4,X3) )
                   => ( v1_borsuk_1(X2,k1_tsep_1(X1,X2,X3))
                      & m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
                      & v1_borsuk_1(X2,k1_tsep_1(X1,X3,X2))
                      & m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tmap_1)).

fof(t33_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) )
                      | ( k2_tsep_1(X1,X3,k1_tsep_1(X1,X2,X4)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & k2_tsep_1(X1,X3,k1_tsep_1(X1,X4,X2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(t22_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(t13_tmap_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_borsuk_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t23_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t43_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X3,X2)
               => ( v1_borsuk_1(k2_tsep_1(X1,X3,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X3,X2),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tmap_1)).

fof(t22_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_borsuk_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ( ( m1_pre_topc(X2,X4)
                        & r1_tsep_1(X4,X3) )
                     => ( v1_borsuk_1(X2,k1_tsep_1(X1,X2,X3))
                        & m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
                        & v1_borsuk_1(X2,k1_tsep_1(X1,X3,X2))
                        & m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_tmap_1])).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33] :
      ( ( k2_tsep_1(X30,X32,k1_tsep_1(X30,X31,X33)) = g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ r1_tsep_1(X32,X33)
        | ~ m1_pre_topc(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( k2_tsep_1(X30,X32,k1_tsep_1(X30,X33,X31)) = g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ r1_tsep_1(X32,X33)
        | ~ m1_pre_topc(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( k2_tsep_1(X30,X32,k1_tsep_1(X30,X31,X33)) = g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ r1_tsep_1(X33,X32)
        | ~ m1_pre_topc(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( k2_tsep_1(X30,X32,k1_tsep_1(X30,X33,X31)) = g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ r1_tsep_1(X33,X32)
        | ~ m1_pre_topc(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_tmap_1])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & v1_borsuk_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk4_0)
    & r1_tsep_1(esk4_0,esk3_0)
    & ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
      | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_struct_0(k1_tsep_1(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10) )
      & ( v1_pre_topc(k1_tsep_1(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10) )
      & ( m1_pre_topc(k1_tsep_1(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_16,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ m1_pre_topc(X24,X23)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X23)
      | m1_pre_topc(X24,k1_tsep_1(X23,X24,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( v2_struct_0(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,X7)
      | k1_tsep_1(X7,X8,X9) = k1_tsep_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

cnf(c_0_18,plain,
    ( k2_tsep_1(X1,X2,k1_tsep_1(X1,X3,X4)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X17,X18,X19] :
      ( ( v1_borsuk_1(X19,X17)
        | ~ v1_borsuk_1(X18,X17)
        | ~ m1_pre_topc(X18,X17)
        | X19 != g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_pre_topc(X19,X17)
        | ~ v1_borsuk_1(X18,X17)
        | ~ m1_pre_topc(X18,X17)
        | X19 != g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_borsuk_1(X18,X17)
        | ~ v1_borsuk_1(X19,X17)
        | ~ m1_pre_topc(X19,X17)
        | X19 != g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_pre_topc(X18,X17)
        | ~ v1_borsuk_1(X19,X17)
        | ~ m1_pre_topc(X19,X17)
        | X19 != g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_tmap_1])])])])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_32,negated_conjecture,
    ( k2_tsep_1(X1,esk4_0,k1_tsep_1(X1,X2,esk3_0)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_20]),c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_24]),c_0_27])]),c_0_20]),c_0_25])).

fof(c_0_38,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r1_tsep_1(X28,X29)
        | r1_tsep_1(X27,X29)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(X29,X28)
        | r1_tsep_1(X27,X29)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(X28,X29)
        | r1_tsep_1(X29,X27)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(X29,X28)
        | r1_tsep_1(X29,X27)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_39,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24])]),c_0_20]),c_0_25])).

cnf(c_0_40,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v1_borsuk_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_33]),c_0_24]),c_0_27])]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),X15)
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_36])).

cnf(c_0_49,plain,
    ( r1_tsep_1(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_36])).

fof(c_0_52,plain,(
    ! [X34,X35,X36] :
      ( ( v1_borsuk_1(k2_tsep_1(X34,X36,X35),X35)
        | r1_tsep_1(X36,X35)
        | v2_struct_0(X36)
        | ~ v1_borsuk_1(X36,X34)
        | ~ m1_pre_topc(X36,X34)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_pre_topc(k2_tsep_1(X34,X36,X35),X35)
        | r1_tsep_1(X36,X35)
        | v2_struct_0(X36)
        | ~ v1_borsuk_1(X36,X34)
        | ~ m1_pre_topc(X36,X34)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tmap_1])])])])])).

cnf(c_0_53,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_54,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35])]),c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_24])])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_24]),c_0_27])])).

cnf(c_0_57,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_46]),c_0_24])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_24]),c_0_27])]),c_0_25]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_35]),c_0_23]),c_0_24])]),c_0_36]),c_0_20]),c_0_25])).

cnf(c_0_62,plain,
    ( v1_borsuk_1(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( v1_borsuk_1(esk2_0,X1)
    | ~ v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_48]),c_0_58])]),c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_24]),c_0_27])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_51]),c_0_51]),c_0_48])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_46])]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | v1_borsuk_1(k2_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_borsuk_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_24]),c_0_27])]),c_0_25]),c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_58]),c_0_65])]),c_0_66])).

fof(c_0_71,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_tsep_1(X21,X22)
        | ~ m1_pre_topc(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r1_tsep_1(X22,X21)
        | ~ m1_pre_topc(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_33]),c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_33]),c_0_69])]),c_0_70]),c_0_21])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_44])]),c_0_36]),c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_35]),c_0_33]),c_0_24]),c_0_27])]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------
