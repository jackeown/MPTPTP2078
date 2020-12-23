%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t112_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:03 EDT 2019

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 419 expanded)
%              Number of clauses        :   56 ( 148 expanded)
%              Number of leaves         :   18 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  564 (3113 expanded)
%              Number of equality atoms :   36 ( 273 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t112_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',t112_tmap_1)).

fof(t49_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',t49_tmap_1)).

fof(t110_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',t110_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',cc1_pre_topc)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_k6_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_m1_pre_topc)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',fc4_tmap_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',abstractness_v1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_u1_pre_topc)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',d9_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_k2_tmap_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',d4_tmap_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_k2_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_k6_partfun1)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',d10_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_k7_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t112_tmap_1.p',dt_l1_pre_topc)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( u1_struct_0(X3) = X2
                 => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                    & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                    & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                    & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t112_tmap_1])).

fof(c_0_19,plain,(
    ! [X113,X114,X115,X116] :
      ( ( ~ v5_pre_topc(X115,X114,X113)
        | ~ m1_subset_1(X116,u1_struct_0(X114))
        | r1_tmap_1(X114,X113,X115,X116)
        | ~ v1_funct_1(X115)
        | ~ v1_funct_2(X115,u1_struct_0(X114),u1_struct_0(X113))
        | ~ m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X114),u1_struct_0(X113))))
        | v2_struct_0(X114)
        | ~ v2_pre_topc(X114)
        | ~ l1_pre_topc(X114)
        | v2_struct_0(X113)
        | ~ v2_pre_topc(X113)
        | ~ l1_pre_topc(X113) )
      & ( m1_subset_1(esk11_3(X113,X114,X115),u1_struct_0(X114))
        | v5_pre_topc(X115,X114,X113)
        | ~ v1_funct_1(X115)
        | ~ v1_funct_2(X115,u1_struct_0(X114),u1_struct_0(X113))
        | ~ m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X114),u1_struct_0(X113))))
        | v2_struct_0(X114)
        | ~ v2_pre_topc(X114)
        | ~ l1_pre_topc(X114)
        | v2_struct_0(X113)
        | ~ v2_pre_topc(X113)
        | ~ l1_pre_topc(X113) )
      & ( ~ r1_tmap_1(X114,X113,X115,esk11_3(X113,X114,X115))
        | v5_pre_topc(X115,X114,X113)
        | ~ v1_funct_1(X115)
        | ~ v1_funct_2(X115,u1_struct_0(X114),u1_struct_0(X113))
        | ~ m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X114),u1_struct_0(X113))))
        | v2_struct_0(X114)
        | ~ v2_pre_topc(X114)
        | ~ l1_pre_topc(X114)
        | v2_struct_0(X113)
        | ~ v2_pre_topc(X113)
        | ~ l1_pre_topc(X113) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_20,plain,(
    ! [X98,X99,X100,X101] :
      ( v2_struct_0(X98)
      | ~ v2_pre_topc(X98)
      | ~ l1_pre_topc(X98)
      | ~ m1_subset_1(X99,k1_zfmisc_1(u1_struct_0(X98)))
      | v2_struct_0(X100)
      | ~ m1_pre_topc(X100,X98)
      | u1_struct_0(X100) != X99
      | ~ m1_subset_1(X101,u1_struct_0(X100))
      | r1_tmap_1(X100,k6_tmap_1(X98,X99),k2_tmap_1(X98,k6_tmap_1(X98,X99),k7_tmap_1(X98,X99),X100),X101) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

fof(c_0_21,plain,(
    ! [X129,X130] :
      ( ~ v2_pre_topc(X129)
      | ~ l1_pre_topc(X129)
      | ~ m1_pre_topc(X130,X129)
      | v2_pre_topc(X130) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X49,X50] :
      ( ( v1_pre_topc(k6_tmap_1(X49,X50))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))) )
      & ( v2_pre_topc(k6_tmap_1(X49,X50))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))) )
      & ( l1_pre_topc(k6_tmap_1(X49,X50))
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_23,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_pre_topc(X60,X59)
      | l1_pre_topc(X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_24,plain,(
    ! [X131,X132] :
      ( ( ~ v2_struct_0(k6_tmap_1(X131,X132))
        | v2_struct_0(X131)
        | ~ v2_pre_topc(X131)
        | ~ l1_pre_topc(X131)
        | ~ m1_subset_1(X132,k1_zfmisc_1(u1_struct_0(X131))) )
      & ( v1_pre_topc(k6_tmap_1(X131,X132))
        | v2_struct_0(X131)
        | ~ v2_pre_topc(X131)
        | ~ l1_pre_topc(X131)
        | ~ m1_subset_1(X132,k1_zfmisc_1(u1_struct_0(X131))) )
      & ( v2_pre_topc(k6_tmap_1(X131,X132))
        | v2_struct_0(X131)
        | ~ v2_pre_topc(X131)
        | ~ l1_pre_topc(X131)
        | ~ m1_subset_1(X132,k1_zfmisc_1(u1_struct_0(X131))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

fof(c_0_25,plain,(
    ! [X75,X76,X77,X78] :
      ( ( X75 = X77
        | g1_pre_topc(X75,X76) != g1_pre_topc(X77,X78)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k1_zfmisc_1(X75))) )
      & ( X76 = X78
        | g1_pre_topc(X75,X76) != g1_pre_topc(X77,X78)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k1_zfmisc_1(X75))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_26,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | ~ v1_pre_topc(X9)
      | X9 = g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_27,plain,(
    ! [X61] :
      ( ~ l1_pre_topc(X61)
      | m1_subset_1(u1_pre_topc(X61),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X61)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & u1_struct_0(esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k6_tmap_1(esk1_0,esk2_0))
      | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_29,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk11_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | k6_tmap_1(X30,X31) = g1_pre_topc(u1_struct_0(X30),k5_tmap_1(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k6_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != X2
    | ~ v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(esk11_3(k6_tmap_1(X1,X2),X3,k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)),u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,plain,
    ( u1_struct_0(X1) = X2
    | X1 != g1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_tmap_1(X38,X39,X40,X41))
        | ~ l1_struct_0(X38)
        | ~ l1_struct_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X41) )
      & ( v1_funct_2(k2_tmap_1(X38,X39,X40,X41),u1_struct_0(X41),u1_struct_0(X39))
        | ~ l1_struct_0(X38)
        | ~ l1_struct_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X41) )
      & ( m1_subset_1(k2_tmap_1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39))))
        | ~ l1_struct_0(X38)
        | ~ l1_struct_0(X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
        | ~ l1_struct_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k6_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk2_0,u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

cnf(c_0_48,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_55,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk2_0,u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_41]),c_0_41]),c_0_49]),c_0_41]),c_0_50]),c_0_51]),c_0_52])]),c_0_53]),c_0_54])).

cnf(c_0_59,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_55]),c_0_34]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,u1_struct_0(X2))))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_41])).

cnf(c_0_61,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk2_0,u1_struct_0(esk1_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X2,X3),X4,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(k6_tmap_1(X2,X3))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,esk3_0),esk2_0,u1_struct_0(X2))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_41])).

fof(c_0_65,plain,(
    ! [X24,X25,X26,X27] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
      | ~ m1_pre_topc(X27,X24)
      | k2_tmap_1(X24,X25,X26,X27) = k2_partfun1(u1_struct_0(X24),u1_struct_0(X25),X26,u1_struct_0(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_66,negated_conjecture,
    ( ~ l1_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk2_0,u1_struct_0(esk1_0))
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X2,X3),X4,esk3_0),esk2_0,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ l1_struct_0(k6_tmap_1(X2,X3))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_69,plain,(
    ! [X34,X35,X36,X37] :
      ( ( v1_funct_1(k2_partfun1(X34,X35,X36,X37))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( m1_subset_1(k2_partfun1(X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_70,plain,(
    ! [X47] :
      ( v1_partfun1(k6_partfun1(X47),X47)
      & m1_subset_1(k6_partfun1(X47),k1_zfmisc_1(k2_zfmisc_1(X47,X47))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_71,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k7_tmap_1(X22,X23) = k6_partfun1(u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_72,negated_conjecture,
    ( ~ l1_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_73,plain,
    ( k2_tmap_1(X1,k6_tmap_1(X2,X3),X4,X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X4,u1_struct_0(X5))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_59]),c_0_32]),c_0_34]),c_0_35])).

cnf(c_0_74,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_77,plain,(
    ! [X53,X54] :
      ( ( v1_funct_1(k7_tmap_1(X53,X54))
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53))) )
      & ( v1_funct_2(k7_tmap_1(X53,X54),u1_struct_0(X53),u1_struct_0(k6_tmap_1(X53,X54)))
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53))) )
      & ( m1_subset_1(k7_tmap_1(X53,X54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(k6_tmap_1(X53,X54)))))
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_78,negated_conjecture,
    ( ~ l1_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_41]),c_0_49]),c_0_50]),c_0_51]),c_0_52])]),c_0_54]),c_0_74])).

cnf(c_0_79,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( ~ l1_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_82,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_84,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_85,plain,(
    ! [X58] :
      ( ~ l1_pre_topc(X58)
      | l1_struct_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_86,negated_conjecture,
    ( ~ l1_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_87,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_34]),c_0_50]),c_0_51]),c_0_52])]),c_0_54])).

cnf(c_0_90,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_49]),c_0_51])])).

cnf(c_0_91,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_87]),c_0_90])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_87]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
