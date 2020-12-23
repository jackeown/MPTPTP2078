%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:36 EST 2020

% Result     : Theorem 15.13s
% Output     : CNFRefutation 15.13s
% Verified   : 
% Statistics : Number of formulae       :  380 (20308 expanded)
%              Number of clauses        :  272 (6314 expanded)
%              Number of leaves         :   19 (4854 expanded)
%              Depth                    :   39
%              Number of atoms          : 3114 (279788 expanded)
%              Number of equality atoms :  926 (19035 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   32 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( sP0(X3,X2,X1,X0)
    <=> ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(X4) )
          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP0(X3,X2,X1,X0)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
            & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
            & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
            & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(X4) )
            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP0(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0)
            & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4))
            & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0)
            & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5))
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4))
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
          | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          | ~ v1_funct_1(sK3(X0,X1,X2,X3)) )
        & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0)
        & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)))
        & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0)
        & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)))
        & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(sK3(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(sK3(X0,X1,X2,X3)) )
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)))
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)))
          & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(sK3(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5))
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(sK3(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) )
                           => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( sP0(X3,X2,X1,X0)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f36])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP0(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( sP0(X3,X2,X1,X0)
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP0(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( sP0(X3,X2,X1,X0)
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP0(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X4] :
                        ( sP0(X4,X2,X1,X0)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X3,X2,X1,X0)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP0(sK4(X0,X1,X2),X2,X1,X0)
        & l1_pre_topc(sK4(X0,X1,X2))
        & v2_pre_topc(sK4(X0,X1,X2))
        & ~ v2_struct_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ( ~ sP0(sK4(X0,X1,X2),X2,X1,X0)
                    & l1_pre_topc(sK4(X0,X1,X2))
                    & v2_pre_topc(sK4(X0,X1,X2))
                    & ~ v2_struct_0(sK4(X0,X1,X2)) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X4] :
                        ( sP0(X4,X2,X1,X0)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ sP0(sK4(X0,X1,X2),X2,X1,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | l1_pre_topc(sK4(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v2_pre_topc(sK4(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ( ! [X3] :
            ( ! [X4] :
                ( sP1(X3,X2,X1,X0,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,X1,X3)
                | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ~ sP1(X3,X2,X1,X0,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( sP1(X3,X2,X1,X0,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,X1,X3)
                  | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ~ sP1(X3,X2,X1,X0,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( sP1(X3,X2,X1,X0,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,X1,X3)
                  | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ~ sP1(X3,X2,X1,X0,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( sP1(X5,X2,X1,X0,X6)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                  | ~ v5_pre_topc(X6,X1,X5)
                  | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5))
                  | ~ v1_funct_1(X6) )
              | ~ l1_pre_topc(X5)
              | ~ v2_pre_topc(X5)
              | v2_struct_0(X5) )
          & r1_tsep_1(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ sP1(X3,X2,X1,X0,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          & v5_pre_topc(X4,X1,X3)
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
          & v1_funct_1(X4) )
     => ( ~ sP1(X3,X2,X1,X0,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
        & v5_pre_topc(sK6(X0,X1,X2),X1,X3)
        & v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X3))
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ sP1(X3,X2,X1,X0,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(X4,X1,X3)
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
            & v5_pre_topc(X4,X1,sK5(X0,X1,X2))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK5(X0,X1,X2))
        & v2_pre_topc(sK5(X0,X1,X2))
        & ~ v2_struct_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
          & v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
          & v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
          & v1_funct_1(sK6(X0,X1,X2))
          & l1_pre_topc(sK5(X0,X1,X2))
          & v2_pre_topc(sK5(X0,X1,X2))
          & ~ v2_struct_0(sK5(X0,X1,X2)) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( sP1(X5,X2,X1,X0,X6)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                  | ~ v5_pre_topc(X6,X1,X5)
                  | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5))
                  | ~ v1_funct_1(X6) )
              | ~ l1_pre_topc(X5)
              | ~ v2_pre_topc(X5)
              | v2_struct_0(X5) )
          & r1_tsep_1(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f55,f57,f56])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP1(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
            & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(X5,X2,X3)
          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f59,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP1(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
              | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(X5,X2,X3)
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(X5) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
              & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(X5,X2,X3)
            | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(X5) )
        | ~ sP1(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
              | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(X5,X1,X0)
            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X5) ) )
      & ( ! [X6] :
            ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6)) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X6,X1,X0)
            | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X6) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X5,X1,X0)
          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
          | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0)
        & v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK7(X0,X1,X2,X3,X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) )
          & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0)
          & v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(sK7(X0,X1,X2,X3,X4)) ) )
      & ( ! [X6] :
            ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6)) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X6,X1,X0)
            | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X6) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v1_funct_1(sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | l1_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v2_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X1,X3)
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(X5,X2,X3)
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(X4,X1,X3)
                              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(X5,X2,X3)
                                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(X5) )
                               => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                  & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                  & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                  & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> sP2(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f39,f38])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP2(X0,X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP2(X0,X1,X2)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP2(X0,X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP2(X0,X1,X2)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ sP2(X0,X1,X2)
            | ~ r3_tsep_1(X0,X1,X2) )
          & ( sP2(X0,X1,X2)
            | r3_tsep_1(X0,X1,X2) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ sP2(X0,X1,sK10)
          | ~ r3_tsep_1(X0,X1,sK10) )
        & ( sP2(X0,X1,sK10)
          | r3_tsep_1(X0,X1,sK10) )
        & m1_pre_topc(sK10,X0)
        & ~ v2_struct_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP2(X0,X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP2(X0,X1,X2)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ sP2(X0,sK9,X2)
              | ~ r3_tsep_1(X0,sK9,X2) )
            & ( sP2(X0,sK9,X2)
              | r3_tsep_1(X0,sK9,X2) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK9,X0)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ sP2(X0,X1,X2)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( sP2(X0,X1,X2)
                  | r3_tsep_1(X0,X1,X2) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP2(sK8,X1,X2)
                | ~ r3_tsep_1(sK8,X1,X2) )
              & ( sP2(sK8,X1,X2)
                | r3_tsep_1(sK8,X1,X2) )
              & m1_pre_topc(X2,sK8)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK8)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ sP2(sK8,sK9,sK10)
      | ~ r3_tsep_1(sK8,sK9,sK10) )
    & ( sP2(sK8,sK9,sK10)
      | r3_tsep_1(sK8,sK9,sK10) )
    & m1_pre_topc(sK10,sK8)
    & ~ v2_struct_0(sK10)
    & m1_pre_topc(sK9,sK8)
    & ~ v2_struct_0(sK9)
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f64,f67,f66,f65])).

fof(f136,plain,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f68])).

fof(f128,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f129,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f131,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f132,plain,(
    m1_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f133,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f68])).

fof(f134,plain,(
    m1_pre_topc(sK10,sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r3_tsep_1(X0,X1,X2)
       => r3_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r3_tsep_1(X0,X2,X1)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r3_tsep_1(X0,X2,X1)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X2,X1)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f135,plain,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( sP1(X5,X2,X1,X0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
      | ~ v5_pre_topc(X6,X1,X5)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X6,X1,X0)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X6)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1254,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2774,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_32,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1240,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58),X0_59,k10_tmap_1(X0_58,X3_58,X1_58,X2_58,k3_tmap_1(X0_58,X3_58,k1_tsep_1(X0_58,X1_58,X2_58),X1_58,X0_59),k3_tmap_1(X0_58,X3_58,k1_tsep_1(X0_58,X1_58,X2_58),X2_58,X0_59)))
    | ~ v1_funct_2(X0_59,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58))))
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X3_58)
    | ~ v1_funct_1(X0_59)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X3_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2788,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58),X0_59,k10_tmap_1(X0_58,X3_58,X1_58,X2_58,k3_tmap_1(X0_58,X3_58,k1_tsep_1(X0_58,X1_58,X2_58),X1_58,X0_59),k3_tmap_1(X0_58,X3_58,k1_tsep_1(X0_58,X1_58,X2_58),X2_58,X0_59))) = iProver_top
    | v1_funct_2(X0_59,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1267,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | m1_subset_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X2_58,X3_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ v2_pre_topc(X3_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | ~ l1_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2761,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58)))) = iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_7,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1261,plain,
    ( ~ r2_funct_2(X0_60,X1_60,X0_59,X1_59)
    | ~ v1_funct_2(X1_59,X0_60,X1_60)
    | ~ v1_funct_2(X0_59,X0_60,X1_60)
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | X1_59 = X0_59 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2767,plain,
    ( X0_59 = X1_59
    | r2_funct_2(X0_60,X1_60,X1_59,X0_59) != iProver_top
    | v1_funct_2(X1_59,X0_60,X1_60) != iProver_top
    | v1_funct_2(X0_59,X0_60,X1_60) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_6227,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59) = X2_59
    | r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58),X2_59,k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X2_59,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X2_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X2_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_2767])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0))
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1265,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X2_58,X3_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ v2_pre_topc(X3_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59))
    | ~ l1_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2763,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59)) = iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1266,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | v1_funct_2(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X2_58,X3_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ v2_pre_topc(X3_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | ~ l1_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2762,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1266])).

cnf(c_11798,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59) = X2_59
    | r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58),X2_59,k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59)) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X2_59,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X2_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X2_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6227,c_2763,c_2762])).

cnf(c_11802,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,X0_59),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,X0_59)) = X0_59
    | v1_funct_2(X0_59,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,X0_59),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,X0_59),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,X0_59)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,X0_59)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_11798])).

cnf(c_16736,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_11802])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(sK3(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1248,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(sK3(X0_58,X1_58,X2_58,X3_58)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2780,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK3(X0_58,X1_58,X2_58,X3_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1255,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2773,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1251,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2777,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1250,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(sK3(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2778,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(sK3(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1258,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2770,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1249,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(sK3(X0_58,X1_58,X2_58,X3_58),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2779,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(sK3(X0_58,X1_58,X2_58,X3_58),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1256,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2772,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1252,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2776,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_17797,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16736,c_2780,c_2773,c_2777,c_2778,c_2770,c_2779,c_2772,c_2776])).

cnf(c_26,plain,
    ( ~ sP0(sK4(X0,X1,X2),X2,X1,X0)
    | r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1246,plain,
    ( ~ sP0(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2782,plain,
    ( sP0(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58) != iProver_top
    | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_17799,plain,
    ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK4(X0_58,X1_58,X2_58)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK4(X0_58,X1_58,X2_58)) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(sK4(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17797,c_2782])).

cnf(c_27,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4(X0,X1,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1245,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | l1_pre_topc(sK4(X0_58,X1_58,X2_58))
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1354,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK4(X0_58,X1_58,X2_58)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_28,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1244,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | v2_pre_topc(sK4(X0_58,X1_58,X2_58))
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1355,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK4(X0_58,X1_58,X2_58)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_29,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1243,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | ~ v2_struct_0(sK4(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1356,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(sK4(X0_58,X1_58,X2_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_17802,plain,
    ( v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17799,c_1354,c_1355,c_1356])).

cnf(c_17803,plain,
    ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_17802])).

cnf(c_37,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ r3_tsep_1(X0,X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1235,plain,
    ( r4_tsep_1(X0_58,X1_58,X2_58)
    | ~ r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_2793,plain,
    ( r4_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_17816,plain,
    ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | r4_tsep_1(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_17803,c_2793])).

cnf(c_41,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1232,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | m1_subset_1(sK6(X0_58,X1_58,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))))) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_2796,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_subset_1(sK6(X0_58,X1_58,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_34,plain,
    ( ~ r4_tsep_1(X0,X1,X2)
    | ~ v5_pre_topc(X3,X2,X4)
    | ~ v5_pre_topc(X5,X1,X4)
    | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1238,plain,
    ( ~ r4_tsep_1(X0_58,X1_58,X2_58)
    | ~ v5_pre_topc(X0_59,X2_58,X3_58)
    | ~ v5_pre_topc(X1_59,X1_58,X3_58)
    | v5_pre_topc(k10_tmap_1(X0_58,X3_58,X1_58,X2_58,X1_59,X0_59),k1_tsep_1(X0_58,X1_58,X2_58),X3_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X3_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X3_58))
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X3_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58))))
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X3_58)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X3_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2790,plain,
    ( r4_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | v5_pre_topc(X0_59,X1_58,X3_58) != iProver_top
    | v5_pre_topc(X1_59,X2_58,X3_58) != iProver_top
    | v5_pre_topc(k10_tmap_1(X0_58,X3_58,X1_58,X2_58,X0_59,X1_59),k1_tsep_1(X0_58,X1_58,X2_58),X3_58) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X3_58)) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X1_58),u1_struct_0(X3_58)) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X3_58)))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58)))) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_50,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1223,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | ~ v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
    | ~ v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))
    | ~ m1_subset_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))))
    | ~ v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) ),
    inference(subtyping,[status(esa)],[c_50])).

cnf(c_2805,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_7312,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_2805])).

cnf(c_51,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1222,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_51])).

cnf(c_1391,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_53,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1220,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_53])).

cnf(c_1397,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_54,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1219,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) ),
    inference(subtyping,[status(esa)],[c_54])).

cnf(c_1400,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1219])).

cnf(c_13257,plain,
    ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7312,c_1391,c_1397,c_1400])).

cnf(c_13258,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_13257])).

cnf(c_2806,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_4592,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X4_58,X5_58) != iProver_top
    | m1_pre_topc(X1_58,X5_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X5_58) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X5_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X5_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2806,c_2763])).

cnf(c_9008,plain,
    ( v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v2_pre_topc(X5_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_pre_topc(X1_58,X5_58) != iProver_top
    | m1_pre_topc(X4_58,X5_58) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X5_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X5_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4592,c_1397,c_1400])).

cnf(c_9009,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X4_58,X5_58) != iProver_top
    | m1_pre_topc(X1_58,X5_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X5_58) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X5_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X5_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_9008])).

cnf(c_13280,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13258,c_9009])).

cnf(c_13285,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2762,c_13280])).

cnf(c_14274,plain,
    ( v1_funct_1(X0_59) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13285,c_1391,c_1397,c_1400])).

cnf(c_14275,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_14274])).

cnf(c_14296,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r4_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | r1_tsep_1(X2_58,X1_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_14275])).

cnf(c_52,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1221,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_1394,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_14541,plain,
    ( v1_funct_1(X0_59) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r4_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | r1_tsep_1(X2_58,X1_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14296,c_1391,c_1394,c_1397,c_1400])).

cnf(c_14542,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r4_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | r1_tsep_1(X2_58,X1_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_14541])).

cnf(c_14566,plain,
    ( sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r4_tsep_1(X4_58,X1_58,X3_58) != iProver_top
    | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58)) != iProver_top
    | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | r1_tsep_1(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X4_58) != iProver_top
    | m1_pre_topc(X1_58,X4_58) != iProver_top
    | v2_pre_topc(X4_58) != iProver_top
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) != iProver_top
    | v1_funct_1(sK6(X0_58,X1_58,X2_58)) != iProver_top
    | l1_pre_topc(X4_58) != iProver_top
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_14542])).

cnf(c_42,plain,
    ( sP2(X0,X1,X2)
    | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1231,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58))
    | ~ r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_1378,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58)) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_43,plain,
    ( sP2(X0,X1,X2)
    | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1230,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58)))
    | ~ r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_1379,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_44,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | v1_funct_1(sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1229,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | v1_funct_1(sK6(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_1380,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | v1_funct_1(sK6(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1229])).

cnf(c_45,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | l1_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1228,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_1381,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1228])).

cnf(c_46,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | v2_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1227,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_1382,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_47,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ v2_struct_0(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1226,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ v2_struct_0(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_47])).

cnf(c_1383,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | v2_struct_0(sK5(X0_58,X1_58,X2_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(c_15318,plain,
    ( v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r4_tsep_1(X4_58,X1_58,X3_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | r1_tsep_1(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X4_58) != iProver_top
    | m1_pre_topc(X1_58,X4_58) != iProver_top
    | v2_pre_topc(X4_58) != iProver_top
    | l1_pre_topc(X4_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14566,c_1378,c_1379,c_1380,c_1381,c_1382,c_1383])).

cnf(c_15319,plain,
    ( sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r4_tsep_1(X4_58,X1_58,X3_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | r1_tsep_1(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X4_58) != iProver_top
    | m1_pre_topc(X1_58,X4_58) != iProver_top
    | v2_pre_topc(X4_58) != iProver_top
    | l1_pre_topc(X4_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_15318])).

cnf(c_40,plain,
    ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
    | sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1233,plain,
    ( ~ sP1(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58,sK6(X0_58,X1_58,X2_58))
    | sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_2795,plain,
    ( sP1(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58,sK6(X0_58,X1_58,X2_58)) != iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_15336,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r4_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_15319,c_2795])).

cnf(c_18007,plain,
    ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_17816,c_15336])).

cnf(c_59,negated_conjecture,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1214,negated_conjecture,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(subtyping,[status(esa)],[c_59])).

cnf(c_2814,plain,
    ( sP2(sK8,sK9,sK10) != iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_19631,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_18007,c_2814])).

cnf(c_67,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_66,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_65,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_63,negated_conjecture,
    ( m1_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_62,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_61,negated_conjecture,
    ( m1_pre_topc(sK10,sK8) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_3931,plain,
    ( r3_tsep_1(X0_58,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_58)
    | ~ m1_pre_topc(sK9,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_3978,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | ~ v2_struct_0(sK4(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3931])).

cnf(c_3930,plain,
    ( r3_tsep_1(X0_58,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_58)
    | ~ m1_pre_topc(sK9,X0_58)
    | ~ v2_pre_topc(X0_58)
    | v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_3982,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | v2_pre_topc(sK4(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_3929,plain,
    ( r3_tsep_1(X0_58,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_58)
    | ~ m1_pre_topc(sK9,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | l1_pre_topc(sK4(X0_58,sK9,sK10))
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_3986,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | l1_pre_topc(sK4(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3929])).

cnf(c_3928,plain,
    ( ~ sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | r3_tsep_1(X0_58,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_58)
    | ~ m1_pre_topc(sK9,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_3990,plain,
    ( ~ sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_4201,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v1_funct_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_4208,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_1(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_4201])).

cnf(c_4199,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v1_funct_2(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_4216,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_2(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_4199])).

cnf(c_4198,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | m1_subset_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_4220,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | m1_subset_1(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_4198])).

cnf(c_4197,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_4224,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) ),
    inference(instantiation,[status(thm)],[c_4197])).

cnf(c_4196,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_4228,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) ),
    inference(instantiation,[status(thm)],[c_4196])).

cnf(c_4195,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_4232,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_4195])).

cnf(c_4193,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_4240,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_4193])).

cnf(c_4192,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_4244,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_4192])).

cnf(c_4190,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_4252,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_4190])).

cnf(c_9,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r3_tsep_1(X0,X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1259,plain,
    ( ~ r3_tsep_1(X0_58,X1_58,X2_58)
    | r3_tsep_1(X0_58,X2_58,X1_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_49,plain,
    ( ~ sP2(X0,X1,X2)
    | r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1224,plain,
    ( ~ sP2(X0_58,X1_58,X2_58)
    | r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_60,negated_conjecture,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1213,negated_conjecture,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(subtyping,[status(esa)],[c_60])).

cnf(c_3708,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | r1_tsep_1(sK9,sK10) ),
    inference(resolution,[status(thm)],[c_1224,c_1213])).

cnf(c_4109,plain,
    ( r3_tsep_1(sK8,sK10,sK9)
    | r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(resolution,[status(thm)],[c_1259,c_3708])).

cnf(c_38,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1241,plain,
    ( ~ r3_tsep_1(X0_58,X1_58,X2_58)
    | r1_tsep_1(X1_58,X2_58)
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_4021,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_4282,plain,
    ( r1_tsep_1(sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4109,c_67,c_66,c_65,c_64,c_63,c_62,c_61,c_3708,c_4021])).

cnf(c_4744,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58),sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58),k10_tmap_1(X0_58,X3_58,X1_58,X2_58,k3_tmap_1(X0_58,X3_58,k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58)),k3_tmap_1(X0_58,X3_58,k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58))))
    | ~ v1_funct_2(sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58),u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58))
    | ~ m1_subset_1(sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58)),u1_struct_0(X3_58))))
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X3_58)
    | ~ v1_funct_1(sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58))
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X3_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_8784,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)),sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k10_tmap_1(X0_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))))
    | ~ v1_funct_2(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ m1_subset_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,X0_58)
    | ~ m1_pre_topc(sK9,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ v1_funct_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK4(X0_58,sK9,sK10))
    | v2_struct_0(X0_58)
    | v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_4744])).

cnf(c_8786,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)),sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))))
    | ~ v1_funct_2(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK4(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ v1_funct_1(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))
    | ~ l1_pre_topc(sK4(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK4(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_8784])).

cnf(c_6619,plain,
    ( ~ r2_funct_2(X0_60,X1_60,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),X0_59)
    | ~ v1_funct_2(X0_59,X0_60,X1_60)
    | ~ v1_funct_2(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),X0_60,X1_60)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ m1_subset_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))
    | X0_59 = sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_10546,plain,
    ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)),sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k10_tmap_1(X0_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))))
    | ~ v1_funct_2(k10_tmap_1(X0_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))),u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ v1_funct_2(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ m1_subset_1(k10_tmap_1(X0_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ v1_funct_1(k10_tmap_1(X0_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))))
    | ~ v1_funct_1(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))
    | k10_tmap_1(X0_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))) = sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) ),
    inference(instantiation,[status(thm)],[c_6619])).

cnf(c_10548,plain,
    ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)),sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))))
    | ~ v1_funct_2(k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ v1_funct_1(k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))))
    | ~ v1_funct_1(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))
    | k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_10546])).

cnf(c_4902,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58)),u1_struct_0(X3_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X0_58,X4_58)
    | ~ m1_pre_topc(X3_58,X4_58)
    | ~ v2_pre_topc(X4_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k10_tmap_1(X4_58,X1_58,X0_58,X3_58,X0_59,k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58))))
    | ~ v1_funct_1(k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58)))
    | ~ l1_pre_topc(X4_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X3_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X4_58)
    | v2_struct_0(X0_58) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_8977,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(sK10,X2_58)
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(sK4(X1_58,sK9,sK10))
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k10_tmap_1(X2_58,sK4(X1_58,sK9,sK10),X0_58,sK10,X0_59,k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58))))
    | ~ v1_funct_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)))
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(sK4(X1_58,sK9,sK10))
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK4(X1_58,sK9,sK10))
    | v2_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_4902])).

cnf(c_10920,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k10_tmap_1(sK8,sK4(X0_58,sK9,sK10),sK9,sK10,X0_59,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))))
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ l1_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_8977])).

cnf(c_11984,plain,
    ( ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | v1_funct_1(k10_tmap_1(sK8,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))))
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ l1_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_10920])).

cnf(c_11986,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK4(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | v1_funct_1(k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))))
    | ~ v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)))
    | ~ v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)))
    | ~ l1_pre_topc(sK4(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK4(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11984])).

cnf(c_4900,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58)),u1_struct_0(X3_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | m1_subset_1(k10_tmap_1(X4_58,X1_58,X0_58,X3_58,X0_59,k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X4_58,X0_58,X3_58)),u1_struct_0(X1_58))))
    | ~ m1_subset_1(k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X0_58,X4_58)
    | ~ m1_pre_topc(X3_58,X4_58)
    | ~ v2_pre_topc(X4_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k3_tmap_1(X2_58,sK4(X2_58,sK9,sK10),k1_tsep_1(X2_58,sK9,sK10),sK10,sK3(sK4(X2_58,sK9,sK10),sK10,sK9,X2_58)))
    | ~ l1_pre_topc(X4_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X3_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X4_58)
    | v2_struct_0(X0_58) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_8987,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | m1_subset_1(k10_tmap_1(X2_58,sK4(X1_58,sK9,sK10),X0_58,sK10,X0_59,k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_58,X0_58,sK10)),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(sK10,X2_58)
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(sK4(X1_58,sK9,sK10))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)))
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(sK4(X1_58,sK9,sK10))
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK4(X1_58,sK9,sK10))
    | v2_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_4900])).

cnf(c_10964,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | m1_subset_1(k10_tmap_1(X1_58,sK4(X0_58,sK9,sK10),sK9,sK10,X0_59,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,X1_58)
    | ~ m1_pre_topc(sK9,X1_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK4(X0_58,sK9,sK10))
    | v2_struct_0(X1_58)
    | v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_8987])).

cnf(c_12406,plain,
    ( ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | m1_subset_1(k10_tmap_1(X1_58,sK4(X0_58,sK9,sK10),sK9,sK10,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,X1_58)
    | ~ m1_pre_topc(sK9,X1_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK4(X0_58,sK9,sK10))
    | v2_struct_0(X1_58)
    | v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_10964])).

cnf(c_12408,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10)))
    | m1_subset_1(k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK4(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)))
    | ~ v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)))
    | ~ l1_pre_topc(sK4(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK4(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_12406])).

cnf(c_4901,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v1_funct_2(k10_tmap_1(X2_58,X1_58,X0_58,X3_58,X0_59,k3_tmap_1(X4_58,sK4(X4_58,sK9,sK10),k1_tsep_1(X4_58,sK9,sK10),sK10,sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58))),u1_struct_0(k1_tsep_1(X2_58,X0_58,X3_58)),u1_struct_0(X1_58))
    | ~ v1_funct_2(k3_tmap_1(X4_58,sK4(X4_58,sK9,sK10),k1_tsep_1(X4_58,sK9,sK10),sK10,sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58)),u1_struct_0(X3_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(k3_tmap_1(X4_58,sK4(X4_58,sK9,sK10),k1_tsep_1(X4_58,sK9,sK10),sK10,sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k3_tmap_1(X4_58,sK4(X4_58,sK9,sK10),k1_tsep_1(X4_58,sK9,sK10),sK10,sK3(sK4(X4_58,sK9,sK10),sK10,sK9,X4_58)))
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X3_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X0_58) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_8992,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | v1_funct_2(k10_tmap_1(X2_58,sK4(X1_58,sK9,sK10),X0_58,sK10,X0_59,k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58))),u1_struct_0(k1_tsep_1(X2_58,X0_58,sK10)),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(sK10,X2_58)
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(sK4(X1_58,sK9,sK10))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)))
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(sK4(X1_58,sK9,sK10))
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK4(X1_58,sK9,sK10))
    | v2_struct_0(sK10) ),
    inference(instantiation,[status(thm)],[c_4901])).

cnf(c_10982,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | v1_funct_2(k10_tmap_1(X1_58,sK4(X0_58,sK9,sK10),sK9,sK10,X0_59,k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))),u1_struct_0(k1_tsep_1(X1_58,sK9,sK10)),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,X1_58)
    | ~ m1_pre_topc(sK9,X1_58)
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK4(X0_58,sK9,sK10))
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)))
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK4(X0_58,sK9,sK10))
    | v2_struct_0(X1_58)
    | v2_struct_0(sK4(X0_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_8992])).

cnf(c_12411,plain,
    ( v1_funct_2(k10_tmap_1(X0_58,sK4(X1_58,sK9,sK10),sK9,sK10,k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK9,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58))),u1_struct_0(k1_tsep_1(X0_58,sK9,sK10)),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK9,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),u1_struct_0(sK9),u1_struct_0(sK4(X1_58,sK9,sK10)))
    | ~ m1_subset_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK9,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X1_58,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,X0_58)
    | ~ m1_pre_topc(sK9,X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK4(X1_58,sK9,sK10))
    | ~ v1_funct_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK10,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)))
    | ~ v1_funct_1(k3_tmap_1(X1_58,sK4(X1_58,sK9,sK10),k1_tsep_1(X1_58,sK9,sK10),sK9,sK3(sK4(X1_58,sK9,sK10),sK10,sK9,X1_58)))
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK4(X1_58,sK9,sK10))
    | v2_struct_0(X0_58)
    | v2_struct_0(sK4(X1_58,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_10982])).

cnf(c_12413,plain,
    ( v1_funct_2(k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10)))))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK4(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)))
    | ~ v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)))
    | ~ l1_pre_topc(sK4(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK4(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_12411])).

cnf(c_19653,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19631])).

cnf(c_19655,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19631,c_67,c_66,c_65,c_64,c_63,c_62,c_61,c_3708,c_3978,c_3982,c_3986,c_3990,c_4021,c_4208,c_4216,c_4220,c_4224,c_4228,c_4232,c_4240,c_4244,c_4252,c_8786,c_10548,c_11986,c_12408,c_12413,c_19653])).

cnf(c_19671,plain,
    ( r4_tsep_1(sK8,sK9,sK10) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_19655,c_2790])).

cnf(c_68,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_69,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_70,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_71,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_72,plain,
    ( m1_pre_topc(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_73,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_74,plain,
    ( m1_pre_topc(sK10,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_75,plain,
    ( sP2(sK8,sK9,sK10) = iProver_top
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_3989,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) != iProver_top
    | r3_tsep_1(X0_58,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_58) != iProver_top
    | m1_pre_topc(sK9,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3928])).

cnf(c_3991,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) != iProver_top
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3989])).

cnf(c_4020,plain,
    ( r4_tsep_1(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_4032,plain,
    ( r4_tsep_1(sK8,sK9,sK10) = iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4020])).

cnf(c_4284,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4282])).

cnf(c_48,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ sP2(X3,X2,X1)
    | ~ v5_pre_topc(X4,X2,X0)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1225,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | ~ sP2(X3_58,X2_58,X1_58)
    | ~ v5_pre_topc(X0_59,X2_58,X0_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_59)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_2803,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | sP2(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1225])).

cnf(c_7005,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) = iProver_top
    | sP0(X0_58,X5_58,X2_58,X4_58) = iProver_top
    | sP2(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),X2_58,X0_58) != iProver_top
    | v1_funct_2(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_2803])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1253,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),X2_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2775,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),X2_58,X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_12035,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) = iProver_top
    | sP0(X0_58,X5_58,X2_58,X4_58) = iProver_top
    | sP2(X3_58,X2_58,X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7005,c_2777,c_2776,c_2775])).

cnf(c_56,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X5,X1,X0)
    | v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1217,plain,
    ( ~ sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | ~ v5_pre_topc(X1_59,X1_58,X0_58)
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,X1_59),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
    | ~ v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58))))
    | ~ v1_funct_1(X1_59) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_2811,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) != iProver_top
    | v5_pre_topc(X1_59,X1_58,X0_58) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,X1_59),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1217])).

cnf(c_19665,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19655,c_2811])).

cnf(c_20508,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2770,c_19665])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_710,plain,
    ( ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | sP0(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_21,c_20,c_19])).

cnf(c_711,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
    inference(renaming,[status(thm)],[c_710])).

cnf(c_1205,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | ~ v5_pre_topc(sK3(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) ),
    inference(subtyping,[status(esa)],[c_711])).

cnf(c_4200,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | ~ v5_pre_topc(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k1_tsep_1(X0_58,sK9,sK10),sK4(X0_58,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_4211,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v5_pre_topc(sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58),k1_tsep_1(X0_58,sK9,sK10),sK4(X0_58,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4200])).

cnf(c_4213,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4211])).

cnf(c_4227,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4196])).

cnf(c_4229,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4227])).

cnf(c_4243,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4192])).

cnf(c_4245,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4243])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1257,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4191,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v5_pre_topc(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),sK10,sK4(X0_58,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_4247,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v5_pre_topc(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),sK10,sK4(X0_58,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4191])).

cnf(c_4249,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4247])).

cnf(c_20516,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20508,c_4213,c_4229,c_4245,c_4249])).

cnf(c_20523,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | sP2(sK8,sK9,sK10) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12035,c_20516])).

cnf(c_21143,plain,
    ( v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19671,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_75,c_3991,c_4032,c_4284,c_20523])).

cnf(c_21144,plain,
    ( v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_21143])).

cnf(c_21159,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_21144])).

cnf(c_4223,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4197])).

cnf(c_4225,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4223])).

cnf(c_4231,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4195])).

cnf(c_4233,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4231])).

cnf(c_4194,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)
    | v5_pre_topc(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),sK9,sK4(X0_58,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_4235,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | v5_pre_topc(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),sK9,sK4(X0_58,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4194])).

cnf(c_4237,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4235])).

cnf(c_4239,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK9,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(X0_58,sK9,sK10))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4193])).

cnf(c_4241,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK4(sK8,sK9,sK10))))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4239])).

cnf(c_4251,plain,
    ( sP0(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58) = iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,sK4(X0_58,sK9,sK10),k1_tsep_1(X0_58,sK9,sK10),sK10,sK3(sK4(X0_58,sK9,sK10),sK10,sK9,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(X0_58,sK9,sK10))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4190])).

cnf(c_4253,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_21345,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21159,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_75,c_3991,c_4032,c_4213,c_4225,c_4229,c_4233,c_4237,c_4241,c_4245,c_4249,c_4253,c_4284,c_19671,c_20523])).

cnf(c_21353,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_21345,c_2782])).

cnf(c_3977,plain,
    ( r3_tsep_1(X0_58,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_58) != iProver_top
    | m1_pre_topc(sK9,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK4(X0_58,sK9,sK10)) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3931])).

cnf(c_3979,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3977])).

cnf(c_3981,plain,
    ( r3_tsep_1(X0_58,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_58) != iProver_top
    | m1_pre_topc(sK9,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK4(X0_58,sK9,sK10)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3930])).

cnf(c_3983,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) = iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_3985,plain,
    ( r3_tsep_1(X0_58,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_58) != iProver_top
    | m1_pre_topc(sK9,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK4(X0_58,sK9,sK10)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3929])).

cnf(c_3987,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) = iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3985])).

cnf(c_21356,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21353,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_3979,c_3983,c_3987,c_4284])).

cnf(c_21361,plain,
    ( r4_tsep_1(sK8,sK9,sK10) = iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_21356,c_2793])).

cnf(c_21919,plain,
    ( r4_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21361,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_3979,c_3983,c_3987,c_4032,c_4284,c_21353])).

cnf(c_21924,plain,
    ( sP2(sK8,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_21919,c_15336])).

cnf(c_76,plain,
    ( sP2(sK8,sK9,sK10) != iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21924,c_21356,c_4284,c_76,c_74,c_73,c_72,c_71,c_70,c_69,c_68])).


%------------------------------------------------------------------------------
