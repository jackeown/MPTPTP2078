%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t111_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:03 EDT 2019

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 345 expanded)
%              Number of clauses        :   55 ( 124 expanded)
%              Number of leaves         :   18 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  538 (2593 expanded)
%              Number of equality atoms :   32 (  82 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',t49_tmap_1)).

fof(t109_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',t109_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',cc1_pre_topc)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_k6_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_m1_pre_topc)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',fc4_tmap_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',abstractness_v1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_u1_pre_topc)).

fof(t111_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',t111_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',d4_tmap_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',d9_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_k7_tmap_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_k6_partfun1)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',d10_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t111_tmap_1.p',dt_l1_pre_topc)).

fof(c_0_18,plain,(
    ! [X115,X116,X117,X118] :
      ( ( ~ v5_pre_topc(X117,X116,X115)
        | ~ m1_subset_1(X118,u1_struct_0(X116))
        | r1_tmap_1(X116,X115,X117,X118)
        | ~ v1_funct_1(X117)
        | ~ v1_funct_2(X117,u1_struct_0(X116),u1_struct_0(X115))
        | ~ m1_subset_1(X117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X116),u1_struct_0(X115))))
        | v2_struct_0(X116)
        | ~ v2_pre_topc(X116)
        | ~ l1_pre_topc(X116)
        | v2_struct_0(X115)
        | ~ v2_pre_topc(X115)
        | ~ l1_pre_topc(X115) )
      & ( m1_subset_1(esk11_3(X115,X116,X117),u1_struct_0(X116))
        | v5_pre_topc(X117,X116,X115)
        | ~ v1_funct_1(X117)
        | ~ v1_funct_2(X117,u1_struct_0(X116),u1_struct_0(X115))
        | ~ m1_subset_1(X117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X116),u1_struct_0(X115))))
        | v2_struct_0(X116)
        | ~ v2_pre_topc(X116)
        | ~ l1_pre_topc(X116)
        | v2_struct_0(X115)
        | ~ v2_pre_topc(X115)
        | ~ l1_pre_topc(X115) )
      & ( ~ r1_tmap_1(X116,X115,X117,esk11_3(X115,X116,X117))
        | v5_pre_topc(X117,X116,X115)
        | ~ v1_funct_1(X117)
        | ~ v1_funct_2(X117,u1_struct_0(X116),u1_struct_0(X115))
        | ~ m1_subset_1(X117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X116),u1_struct_0(X115))))
        | v2_struct_0(X116)
        | ~ v2_pre_topc(X116)
        | ~ l1_pre_topc(X116)
        | v2_struct_0(X115)
        | ~ v2_pre_topc(X115)
        | ~ l1_pre_topc(X115) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_19,plain,(
    ! [X100,X101,X102,X103] :
      ( v2_struct_0(X100)
      | ~ v2_pre_topc(X100)
      | ~ l1_pre_topc(X100)
      | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
      | v2_struct_0(X102)
      | ~ m1_pre_topc(X102,X100)
      | ~ r1_xboole_0(u1_struct_0(X102),X101)
      | ~ m1_subset_1(X103,u1_struct_0(X102))
      | r1_tmap_1(X102,k6_tmap_1(X100,X101),k2_tmap_1(X100,k6_tmap_1(X100,X101),k7_tmap_1(X100,X101),X102),X103) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).

fof(c_0_20,plain,(
    ! [X131,X132] :
      ( ~ v2_pre_topc(X131)
      | ~ l1_pre_topc(X131)
      | ~ m1_pre_topc(X132,X131)
      | v2_pre_topc(X132) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_pre_topc(X60,X59)
      | l1_pre_topc(X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,plain,(
    ! [X133,X134] :
      ( ( ~ v2_struct_0(k6_tmap_1(X133,X134))
        | v2_struct_0(X133)
        | ~ v2_pre_topc(X133)
        | ~ l1_pre_topc(X133)
        | ~ m1_subset_1(X134,k1_zfmisc_1(u1_struct_0(X133))) )
      & ( v1_pre_topc(k6_tmap_1(X133,X134))
        | v2_struct_0(X133)
        | ~ v2_pre_topc(X133)
        | ~ l1_pre_topc(X133)
        | ~ m1_subset_1(X134,k1_zfmisc_1(u1_struct_0(X133))) )
      & ( v2_pre_topc(k6_tmap_1(X133,X134))
        | v2_struct_0(X133)
        | ~ v2_pre_topc(X133)
        | ~ l1_pre_topc(X133)
        | ~ m1_subset_1(X134,k1_zfmisc_1(u1_struct_0(X133))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

fof(c_0_24,plain,(
    ! [X75,X76,X77,X78] :
      ( ( X75 = X77
        | g1_pre_topc(X75,X76) != g1_pre_topc(X77,X78)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k1_zfmisc_1(X75))) )
      & ( X76 = X78
        | g1_pre_topc(X75,X76) != g1_pre_topc(X77,X78)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k1_zfmisc_1(X75))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_25,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | ~ v1_pre_topc(X9)
      | X9 = g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_26,plain,(
    ! [X61] :
      ( ~ l1_pre_topc(X61)
      | m1_subset_1(u1_pre_topc(X61),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X61)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_xboole_0(u1_struct_0(X3),X2)
                 => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                    & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                    & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                    & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t111_tmap_1])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X87,X88,X89,X90] :
      ( ~ v1_funct_1(X89)
      | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X87,X88)))
      | k2_partfun1(X87,X88,X89,X90) = k7_relat_1(X89,X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_40,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | k6_tmap_1(X30,X31) = g1_pre_topc(u1_struct_0(X30),k5_tmap_1(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

fof(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & r1_xboole_0(u1_struct_0(esk3_0),esk2_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k6_tmap_1(esk1_0,esk2_0))
      | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_42,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(esk11_3(k6_tmap_1(X1,X2),X3,k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)),u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
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

cnf(c_0_47,plain,
    ( u1_struct_0(X1) = X2
    | X1 != g1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k6_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_58,plain,
    ( k2_tmap_1(X1,X2,X3,X4) = k7_relat_1(X3,u1_struct_0(X4))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_59,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_62,plain,(
    ! [X47] :
      ( v1_partfun1(k6_partfun1(X47),X47)
      & m1_subset_1(k6_partfun1(X47),k1_zfmisc_1(k2_zfmisc_1(X47,X47))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_63,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k7_tmap_1(X22,X23) = k6_partfun1(u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_64,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_65,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56]),c_0_57])).

cnf(c_0_67,plain,
    ( k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3) = k7_relat_1(k7_tmap_1(X1,X2),u1_struct_0(X3))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_31]),c_0_33]),c_0_60]),c_0_61]),c_0_34])).

cnf(c_0_68,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_33]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(k7_relat_1(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k7_relat_1(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_57])).

cnf(c_0_72,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk3_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k7_relat_1(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k7_relat_1(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_53]),c_0_54]),c_0_55])]),c_0_57])).

cnf(c_0_75,plain,
    ( k2_tmap_1(X1,X1,k7_tmap_1(X1,X2),X3) = k7_relat_1(k7_tmap_1(X1,X2),u1_struct_0(X3))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_72]),c_0_60]),c_0_73])).

fof(c_0_76,plain,(
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

cnf(c_0_77,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_57])).

cnf(c_0_78,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0))
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_80,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_82,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_72]),c_0_53]),c_0_54]),c_0_55])]),c_0_57])).

cnf(c_0_85,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_73]),c_0_53]),c_0_54]),c_0_55])]),c_0_57])).

fof(c_0_86,plain,(
    ! [X58] :
      ( ~ l1_pre_topc(X58)
      | l1_struct_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_87,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_60]),c_0_53]),c_0_54]),c_0_55])]),c_0_57])).

cnf(c_0_88,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_52]),c_0_54])])).

cnf(c_0_90,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_88]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
