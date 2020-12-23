%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t45_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:15 EDT 2019

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 890 expanded)
%              Number of clauses        :   59 ( 277 expanded)
%              Number of leaves         :   13 ( 217 expanded)
%              Depth                    :   14
%              Number of atoms          :  576 (9919 expanded)
%              Number of equality atoms :   21 (  71 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t45_tmap_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',commutativity_k1_tsep_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',symmetry_r1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t13_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',cc1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t33_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t22_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t43_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',dt_k1_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t23_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t45_tmap_1.p',t22_tmap_1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X14,X12)
      | k1_tsep_1(X12,X13,X14) = k1_tsep_1(X12,X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X37,X38] :
      ( ~ l1_struct_0(X37)
      | ~ l1_struct_0(X38)
      | ~ r1_tsep_1(X37,X38)
      | r1_tsep_1(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | l1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X41,X42,X43] :
      ( ( v1_borsuk_1(X43,X41)
        | ~ v1_borsuk_1(X42,X41)
        | ~ m1_pre_topc(X42,X41)
        | X43 != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_pre_topc(X43,X41)
        | ~ v1_borsuk_1(X42,X41)
        | ~ m1_pre_topc(X42,X41)
        | X43 != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( v1_borsuk_1(X42,X41)
        | ~ v1_borsuk_1(X43,X41)
        | ~ m1_pre_topc(X43,X41)
        | X43 != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_pre_topc(X42,X41)
        | ~ v1_borsuk_1(X43,X41)
        | ~ m1_pre_topc(X43,X41)
        | X43 != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_tmap_1])])])])).

fof(c_0_29,plain,(
    ! [X78,X79] :
      ( ~ v2_pre_topc(X78)
      | ~ l1_pre_topc(X78)
      | ~ m1_pre_topc(X79,X78)
      | v2_pre_topc(X79) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_30,plain,(
    ! [X58,X59,X60,X61] :
      ( ( k2_tsep_1(X58,X60,k1_tsep_1(X58,X59,X61)) = g1_pre_topc(u1_struct_0(X59),u1_pre_topc(X59))
        | ~ r1_tsep_1(X60,X61)
        | ~ m1_pre_topc(X59,X60)
        | v2_struct_0(X61)
        | ~ m1_pre_topc(X61,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( k2_tsep_1(X58,X60,k1_tsep_1(X58,X61,X59)) = g1_pre_topc(u1_struct_0(X59),u1_pre_topc(X59))
        | ~ r1_tsep_1(X60,X61)
        | ~ m1_pre_topc(X59,X60)
        | v2_struct_0(X61)
        | ~ m1_pre_topc(X61,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( k2_tsep_1(X58,X60,k1_tsep_1(X58,X59,X61)) = g1_pre_topc(u1_struct_0(X59),u1_pre_topc(X59))
        | ~ r1_tsep_1(X61,X60)
        | ~ m1_pre_topc(X59,X60)
        | v2_struct_0(X61)
        | ~ m1_pre_topc(X61,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( k2_tsep_1(X58,X60,k1_tsep_1(X58,X61,X59)) = g1_pre_topc(u1_struct_0(X59),u1_pre_topc(X59))
        | ~ r1_tsep_1(X61,X60)
        | ~ m1_pre_topc(X59,X60)
        | v2_struct_0(X61)
        | ~ m1_pre_topc(X61,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_tmap_1])])])])])).

cnf(c_0_31,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])])).

fof(c_0_37,plain,(
    ! [X49,X50,X51] :
      ( v2_struct_0(X49)
      | ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | v2_struct_0(X50)
      | ~ m1_pre_topc(X50,X49)
      | v2_struct_0(X51)
      | ~ m1_pre_topc(X51,X49)
      | m1_pre_topc(X50,k1_tsep_1(X49,X50,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_38,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_tsep_1(X1,X2,k1_tsep_1(X1,X3,X4)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_20])])).

fof(c_0_45,plain,(
    ! [X64,X65,X66] :
      ( ( v1_borsuk_1(k2_tsep_1(X64,X66,X65),X65)
        | r1_tsep_1(X66,X65)
        | v2_struct_0(X66)
        | ~ v1_borsuk_1(X66,X64)
        | ~ m1_pre_topc(X66,X64)
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) )
      & ( m1_pre_topc(k2_tsep_1(X64,X66,X65),X65)
        | r1_tsep_1(X66,X65)
        | v2_struct_0(X66)
        | ~ v1_borsuk_1(X66,X64)
        | ~ m1_pre_topc(X66,X64)
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X64)
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tmap_1])])])])])).

fof(c_0_46,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_struct_0(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( v1_pre_topc(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( v1_borsuk_1(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v1_borsuk_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_38,c_0_39]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_19]),c_0_20]),c_0_42])]),c_0_21]),c_0_22]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_20]),c_0_42])]),c_0_21]),c_0_22])).

cnf(c_0_59,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_27])]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_32]),c_0_20])])).

cnf(c_0_63,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_20]),c_0_42])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,X1),X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_27]),c_0_20]),c_0_42])]),c_0_21]),c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_41]),c_0_32]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_32]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_33])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_41]),c_0_41])])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,X1),X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_54]),c_0_27]),c_0_20]),c_0_42])]),c_0_21]),c_0_52])).

fof(c_0_70,plain,(
    ! [X52,X53,X54,X55] :
      ( ( ~ r1_tsep_1(X54,X55)
        | r1_tsep_1(X53,X55)
        | ~ m1_pre_topc(X53,X54)
        | v2_struct_0(X55)
        | ~ m1_pre_topc(X55,X52)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ r1_tsep_1(X55,X54)
        | r1_tsep_1(X53,X55)
        | ~ m1_pre_topc(X53,X54)
        | v2_struct_0(X55)
        | ~ m1_pre_topc(X55,X52)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ r1_tsep_1(X54,X55)
        | r1_tsep_1(X55,X53)
        | ~ m1_pre_topc(X53,X54)
        | v2_struct_0(X55)
        | ~ m1_pre_topc(X55,X52)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ r1_tsep_1(X55,X54)
        | r1_tsep_1(X55,X53)
        | ~ m1_pre_topc(X53,X54)
        | v2_struct_0(X55)
        | ~ m1_pre_topc(X55,X52)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_71,negated_conjecture,
    ( v1_borsuk_1(esk2_0,X1)
    | ~ v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_65]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_65]),c_0_20]),c_0_42])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_66])).

cnf(c_0_77,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])]),c_0_75]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_52]),c_0_66])).

fof(c_0_80,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_tsep_1(X47,X48)
        | ~ m1_pre_topc(X47,X48)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ r1_tsep_1(X48,X47)
        | ~ m1_pre_topc(X47,X48)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_68]),c_0_33])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_65]),c_0_27]),c_0_32]),c_0_20]),c_0_42])]),c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_51])]),c_0_52]),c_0_33])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_42]),c_0_32]),c_0_27]),c_0_20])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
