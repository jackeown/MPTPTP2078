%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:26 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
% Verified   : 
% Statistics : Number of formulae       :  391 (4082 expanded)
%              Number of clauses        :  283 (1042 expanded)
%              Number of leaves         :   18 (1129 expanded)
%              Depth                    :   33
%              Number of atoms          : 3401 (55552 expanded)
%              Number of equality atoms : 1042 (2586 expanded)
%              Maximal formula depth    :   31 (   9 average)
%              Maximal clause size      :   32 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
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

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f26,plain,(
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

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f46,f45])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(sK3(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f24,plain,(
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
    inference(definition_folding,[],[f16,f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f25,plain,(
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

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f49,f50])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v1_funct_1(sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | l1_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v2_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f27,plain,(
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
    inference(definition_folding,[],[f22,f26,f25])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f53,f56,f55,f54])).

fof(f125,plain,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f57])).

fof(f117,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f118,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f119,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f120,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    m1_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f122,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f57])).

fof(f123,plain,(
    m1_pre_topc(sK10,sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X6,X1,X0)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X6)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11850,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_13220,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11850])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11852,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_13218,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11852])).

cnf(c_48,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ sP2(X3,X2,X1)
    | ~ v5_pre_topc(X4,X2,X0)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11830,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | ~ sP2(X3_58,X2_58,X1_58)
    | ~ v5_pre_topc(X0_59,X2_58,X0_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_13240,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | sP2(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11830])).

cnf(c_16983,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) = iProver_top
    | sP0(X0_58,X5_58,X2_58,X4_58) = iProver_top
    | sP2(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),X2_58,X0_58) != iProver_top
    | v1_funct_2(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13218,c_13240])).

cnf(c_17765,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) = iProver_top
    | sP0(X0_58,X5_58,X2_58,X4_58) = iProver_top
    | sP2(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),X2_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13220,c_16983])).

cnf(c_22,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(sK3(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11846,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(sK3(X0_58,X1_58,X2_58,X3_58)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_13224,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(sK3(X0_58,X1_58,X2_58,X3_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11846])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11847,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(sK3(X0_58,X1_58,X2_58,X3_58),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_13223,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(sK3(X0_58,X1_58,X2_58,X3_58),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11847])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_11849,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_13221,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11849])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_11853,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_13217,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11853])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11848,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(sK3(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_13222,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(sK3(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11848])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_11854,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_13216,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11854])).

cnf(c_0,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_11867,plain,
    ( r2_funct_2(X0_60,X1_60,X0_59,X0_59)
    | ~ v1_funct_2(X0_59,X0_60,X1_60)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X0_59) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_13203,plain,
    ( r2_funct_2(X0_60,X1_60,X0_59,X0_59) = iProver_top
    | v1_funct_2(X0_59,X0_60,X1_60) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11867])).

cnf(c_16040,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13218,c_13203])).

cnf(c_11922,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11850])).

cnf(c_11923,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11849])).

cnf(c_17408,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16040,c_11922,c_11923])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11856,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_13214,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11856])).

cnf(c_15878,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | r2_funct_2(u1_struct_0(X1_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13214,c_13203])).

cnf(c_11918,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11854])).

cnf(c_11919,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11853])).

cnf(c_17397,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
    | r2_funct_2(u1_struct_0(X1_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15878,c_11918,c_11919])).

cnf(c_3,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X6)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | k10_tmap_1(X2,X1,X3,X0,X6,X5) = X4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11864,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,k1_tsep_1(X2_58,X3_58,X0_58),X0_58,X0_59),X1_59)
    | ~ r2_funct_2(u1_struct_0(X3_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,k1_tsep_1(X2_58,X3_58,X0_58),X3_58,X0_59),X2_59)
    | ~ v1_funct_2(X1_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X2_59,u1_struct_0(X3_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X0_59,u1_struct_0(k1_tsep_1(X2_58,X3_58,X0_58)),u1_struct_0(X1_58))
    | ~ r1_tsep_1(X3_58,X0_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X2_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_58,X3_58,X0_58)),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X2_59)
    | k10_tmap_1(X2_58,X1_58,X3_58,X0_58,X2_59,X1_59) = X0_59 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_13206,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59) = X2_59
    | r2_funct_2(u1_struct_0(X3_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,X2_59),X1_59) != iProver_top
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,X2_59),X0_59) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X2_59,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X2_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v1_funct_1(X2_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11864])).

cnf(c_17403,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),X0_59) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17397,c_13206])).

cnf(c_19370,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),X0_59) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13214,c_17403])).

cnf(c_28392,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17408,c_19370])).

cnf(c_38536,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13218,c_28392])).

cnf(c_38553,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13216,c_38536])).

cnf(c_38556,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13220,c_38553])).

cnf(c_38580,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13222,c_38556])).

cnf(c_38584,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13217,c_38580])).

cnf(c_38625,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13221,c_38584])).

cnf(c_38769,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13223,c_38625])).

cnf(c_38772,plain,
    ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
    | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
    | r1_tsep_1(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_13224,c_38769])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f90])).

cnf(c_11844,plain,
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
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_13226,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_11844])).

cnf(c_38830,plain,
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
    inference(superposition,[status(thm)],[c_38772,c_13226])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f89])).

cnf(c_11843,plain,
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
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_11931,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_11843])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f88])).

cnf(c_11842,plain,
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
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_11932,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_11842])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f87])).

cnf(c_11841,plain,
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
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_11933,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_11841])).

cnf(c_38833,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_38830,c_11931,c_11932,c_11933])).

cnf(c_38834,plain,
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
    inference(renaming,[status(thm)],[c_38833])).

cnf(c_41,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_11837,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | m1_subset_1(sK6(X0_58,X1_58,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))))) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_13233,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_subset_1(sK6(X0_58,X1_58,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11837])).

cnf(c_51,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_11827,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
    inference(subtyping,[status(esa)],[c_51])).

cnf(c_13243,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11827])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11857,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X2_58,X3_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X3_58)
    | ~ v2_pre_topc(X1_58)
    | ~ l1_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59)
    | v1_funct_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_13213,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11857])).

cnf(c_17139,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X5_58) != iProver_top
    | m1_pre_topc(X4_58,X5_58) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X5_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X5_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X5_58) = iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13243,c_13213])).

cnf(c_53,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_11825,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_53])).

cnf(c_11957,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11825])).

cnf(c_54,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_11824,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) ),
    inference(subtyping,[status(esa)],[c_54])).

cnf(c_11960,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11824])).

cnf(c_18104,plain,
    ( v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v2_struct_0(X5_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X5_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X5_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X4_58,X5_58) != iProver_top
    | m1_pre_topc(X1_58,X5_58) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17139,c_11957,c_11960])).

cnf(c_18105,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X5_58) != iProver_top
    | m1_pre_topc(X4_58,X5_58) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X5_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X5_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X5_58) = iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top ),
    inference(renaming,[status(thm)],[c_18104])).

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
    inference(cnf_transformation,[],[f97])).

cnf(c_34,plain,
    ( ~ r4_tsep_1(X0,X1,X2)
    | ~ v5_pre_topc(X3,X2,X4)
    | ~ v5_pre_topc(X5,X1,X4)
    | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1048,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | ~ v5_pre_topc(X3,X2,X4)
    | ~ v5_pre_topc(X5,X1,X4)
    | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5) ),
    inference(resolution,[status(thm)],[c_37,c_34])).

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
    inference(cnf_transformation,[],[f96])).

cnf(c_1052,plain,
    ( ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
    | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
    | ~ v5_pre_topc(X5,X1,X4)
    | ~ v5_pre_topc(X3,X2,X4)
    | ~ r3_tsep_1(X0,X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1048,c_38,c_37,c_34])).

cnf(c_1053,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | ~ v5_pre_topc(X3,X2,X4)
    | ~ v5_pre_topc(X5,X1,X4)
    | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5) ),
    inference(renaming,[status(thm)],[c_1052])).

cnf(c_11807,plain,
    ( ~ r3_tsep_1(X0_58,X1_58,X2_58)
    | ~ v5_pre_topc(X0_59,X2_58,X3_58)
    | ~ v5_pre_topc(X1_59,X1_58,X3_58)
    | v5_pre_topc(k10_tmap_1(X0_58,X3_58,X1_58,X2_58,X1_59,X0_59),k1_tsep_1(X0_58,X1_58,X2_58),X3_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X3_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X3_58))
    | ~ m1_pre_topc(X2_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X3_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X3_58)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X3_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59) ),
    inference(subtyping,[status(esa)],[c_1053])).

cnf(c_13263,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X3_58) != iProver_top
    | v5_pre_topc(X1_59,X1_58,X3_58) != iProver_top
    | v5_pre_topc(k10_tmap_1(X0_58,X3_58,X1_58,X2_58,X1_59,X0_59),k1_tsep_1(X0_58,X1_58,X2_58),X3_58) = iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X3_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X3_58)) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X3_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11807])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11858,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | v1_funct_2(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X2_58,X3_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X3_58)
    | ~ v2_pre_topc(X1_58)
    | ~ l1_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_13212,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58)) = iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11858])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11859,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X2_58,X3_58)
    | ~ m1_pre_topc(X0_58,X3_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | m1_subset_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X3_58)
    | ~ v2_pre_topc(X1_58)
    | ~ l1_pre_topc(X3_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_13211,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X0_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58)))) = iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11859])).

cnf(c_50,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_11828,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | ~ v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
    | ~ v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))
    | ~ m1_subset_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))))
    | ~ v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) ),
    inference(subtyping,[status(esa)],[c_50])).

cnf(c_13242,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11828])).

cnf(c_17609,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13211,c_13242])).

cnf(c_11951,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11827])).

cnf(c_21976,plain,
    ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17609,c_11951,c_11957,c_11960])).

cnf(c_21977,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21976])).

cnf(c_21983,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13212,c_21977])).

cnf(c_23291,plain,
    ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21983,c_11951,c_11957,c_11960])).

cnf(c_23292,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
    inference(renaming,[status(thm)],[c_23291])).

cnf(c_23297,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13263,c_23292])).

cnf(c_52,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_11826,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_11954,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11826])).

cnf(c_27542,plain,
    ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23297,c_11951,c_11954,c_11957,c_11960])).

cnf(c_27543,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
    inference(renaming,[status(thm)],[c_27542])).

cnf(c_27548,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
    | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
    | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
    | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v1_funct_1(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_18105,c_27543])).

cnf(c_27556,plain,
    ( sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r3_tsep_1(X4_58,X1_58,X3_58) != iProver_top
    | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58)) != iProver_top
    | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X3_58,X4_58) != iProver_top
    | m1_pre_topc(X1_58,X4_58) != iProver_top
    | v2_pre_topc(X4_58) != iProver_top
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) != iProver_top
    | l1_pre_topc(X4_58) != iProver_top
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_struct_0(sK5(X0_58,X1_58,X2_58)) = iProver_top
    | v1_funct_1(sK6(X0_58,X1_58,X2_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13233,c_27548])).

cnf(c_42,plain,
    ( sP2(X0,X1,X2)
    | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_11836,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58))
    | ~ r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_11938,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58)) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11836])).

cnf(c_43,plain,
    ( sP2(X0,X1,X2)
    | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_11835,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58)))
    | ~ r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_11939,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11835])).

cnf(c_44,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | v1_funct_1(sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_11834,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | v1_funct_1(sK6(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_11940,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | v1_funct_1(sK6(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11834])).

cnf(c_45,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | l1_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_11833,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_11941,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11833])).

cnf(c_46,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | v2_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_11832,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_11942,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11832])).

cnf(c_47,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ v2_struct_0(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_11831,plain,
    ( sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58)
    | ~ v2_struct_0(sK5(X0_58,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_47])).

cnf(c_11943,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | v2_struct_0(sK5(X0_58,X1_58,X2_58)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11831])).

cnf(c_27682,plain,
    ( l1_pre_topc(X4_58) != iProver_top
    | sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r3_tsep_1(X4_58,X1_58,X3_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X3_58,X4_58) != iProver_top
    | m1_pre_topc(X1_58,X4_58) != iProver_top
    | v2_pre_topc(X4_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27556,c_11938,c_11939,c_11940,c_11941,c_11942,c_11943])).

cnf(c_27683,plain,
    ( sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r3_tsep_1(X4_58,X1_58,X3_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X3_58,X4_58) != iProver_top
    | m1_pre_topc(X1_58,X4_58) != iProver_top
    | v2_pre_topc(X4_58) != iProver_top
    | l1_pre_topc(X4_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X4_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_27682])).

cnf(c_40,plain,
    ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
    | sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_11838,plain,
    ( ~ sP1(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58,sK6(X0_58,X1_58,X2_58))
    | sP2(X0_58,X1_58,X2_58)
    | ~ r1_tsep_1(X1_58,X2_58) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_13232,plain,
    ( sP1(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58,sK6(X0_58,X1_58,X2_58)) != iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11838])).

cnf(c_27688,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(superposition,[status(thm)],[c_27683,c_13232])).

cnf(c_11839,plain,
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

cnf(c_11935,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | r1_tsep_1(X1_58,X2_58) = iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11839])).

cnf(c_27694,plain,
    ( r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | sP2(X0_58,X1_58,X2_58) = iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27688,c_11935])).

cnf(c_27695,plain,
    ( sP2(X0_58,X1_58,X2_58) = iProver_top
    | r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_27694])).

cnf(c_38837,plain,
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
    inference(superposition,[status(thm)],[c_38834,c_27695])).

cnf(c_59,negated_conjecture,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_11819,negated_conjecture,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(subtyping,[status(esa)],[c_59])).

cnf(c_13251,plain,
    ( sP2(sK8,sK9,sK10) != iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11819])).

cnf(c_38906,plain,
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
    inference(superposition,[status(thm)],[c_38837,c_13251])).

cnf(c_67,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_68,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_66,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_69,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_65,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_70,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_71,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( m1_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_72,plain,
    ( m1_pre_topc(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_73,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( m1_pre_topc(sK10,sK8) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_74,plain,
    ( m1_pre_topc(sK10,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_524,plain,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(prop_impl,[status(thm)],[c_59])).

cnf(c_1491,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(X0,X1)
    | ~ v2_struct_0(sK5(X2,X0,X1))
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_47,c_524])).

cnf(c_1492,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ v2_struct_0(sK5(sK8,sK9,sK10)) ),
    inference(unflattening,[status(thm)],[c_1491])).

cnf(c_1493,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_1504,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(X0,X1)
    | v2_pre_topc(sK5(X2,X0,X1))
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_524])).

cnf(c_1505,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | v2_pre_topc(sK5(sK8,sK9,sK10)) ),
    inference(unflattening,[status(thm)],[c_1504])).

cnf(c_1506,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_1517,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(X0,X1)
    | l1_pre_topc(sK5(X2,X0,X1))
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_524])).

cnf(c_1518,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | l1_pre_topc(sK5(sK8,sK9,sK10)) ),
    inference(unflattening,[status(thm)],[c_1517])).

cnf(c_1519,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_1530,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(X0,X1)
    | v1_funct_1(sK6(X2,X0,X1))
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_524])).

cnf(c_1531,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | v1_funct_1(sK6(sK8,sK9,sK10)) ),
    inference(unflattening,[status(thm)],[c_1530])).

cnf(c_1532,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | v1_funct_1(sK6(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1531])).

cnf(c_1543,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
    | ~ r1_tsep_1(X1,X2)
    | sK10 != X2
    | sK9 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_524])).

cnf(c_1544,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ r1_tsep_1(sK9,sK10) ),
    inference(unflattening,[status(thm)],[c_1543])).

cnf(c_1545,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_1556,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
    | ~ r1_tsep_1(X1,X2)
    | sK10 != X2
    | sK9 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_524])).

cnf(c_1557,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10))
    | ~ r1_tsep_1(sK9,sK10) ),
    inference(unflattening,[status(thm)],[c_1556])).

cnf(c_1558,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10)) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_1569,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(X0,X1)
    | m1_subset_1(sK6(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5(X2,X0,X1)))))
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_524])).

cnf(c_1570,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) ),
    inference(unflattening,[status(thm)],[c_1569])).

cnf(c_1571,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_1582,plain,
    ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
    | ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(X1,X2)
    | sK10 != X2
    | sK9 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_524])).

cnf(c_1583,plain,
    ( ~ sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
    | ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10) ),
    inference(unflattening,[status(thm)],[c_1582])).

cnf(c_1584,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) != iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_32,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_60,negated_conjecture,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_526,plain,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(prop_impl,[status(thm)],[c_60])).

cnf(c_6260,plain,
    ( sP2(sK8,sK9,sK10)
    | r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_526])).

cnf(c_6261,plain,
    ( sP2(sK8,sK9,sK10)
    | r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_6260])).

cnf(c_49,plain,
    ( ~ sP2(X0,X1,X2)
    | r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1595,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | r1_tsep_1(X0,X1)
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_49,c_526])).

cnf(c_1596,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | r1_tsep_1(sK9,sK10) ),
    inference(unflattening,[status(thm)],[c_1595])).

cnf(c_6263,plain,
    ( r1_tsep_1(sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6261,c_67,c_66,c_65,c_64,c_63,c_62,c_61,c_59,c_1596])).

cnf(c_6265,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6263])).

cnf(c_14808,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
    | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_11824])).

cnf(c_14809,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
    | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14808])).

cnf(c_14807,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
    | v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_11826])).

cnf(c_14811,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
    | v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14807])).

cnf(c_14806,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
    | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_11825])).

cnf(c_14813,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14806])).

cnf(c_14805,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
    | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_11827])).

cnf(c_14815,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14805])).

cnf(c_14803,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
    | ~ v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10))
    | ~ v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))) ),
    inference(instantiation,[status(thm)],[c_11828])).

cnf(c_14819,plain,
    ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
    | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14803])).

cnf(c_13507,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(sK10,X2_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK10)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k10_tmap_1(X2_58,X1_58,X0_58,sK10,X0_59,X1_59)) ),
    inference(instantiation,[status(thm)],[c_11857])).

cnf(c_24300,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59)) ),
    inference(instantiation,[status(thm)],[c_13507])).

cnf(c_26411,plain,
    ( ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))))
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
    | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_24300])).

cnf(c_26412,plain,
    ( v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))) = iProver_top
    | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26411])).

cnf(c_13506,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
    | v1_funct_2(k10_tmap_1(X2_58,X1_58,X0_58,sK10,X0_59,X1_59),u1_struct_0(k1_tsep_1(X2_58,X0_58,sK10)),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(sK10,X2_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK10)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59) ),
    inference(instantiation,[status(thm)],[c_11858])).

cnf(c_24340,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
    | v1_funct_2(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(X0_58))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59) ),
    inference(instantiation,[status(thm)],[c_13506])).

cnf(c_28149,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,X0_59,sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_24340])).

cnf(c_30136,plain,
    ( v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
    | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_28149])).

cnf(c_30137,plain,
    ( v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))) = iProver_top
    | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30136])).

cnf(c_36825,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(sK10,X2_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
    | m1_subset_1(k10_tmap_1(X2_58,X1_58,X0_58,sK10,X0_59,X1_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_58,X0_58,sK10)),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK10)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59) ),
    inference(instantiation,[status(thm)],[c_11859])).

cnf(c_37069,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
    | m1_subset_1(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59) ),
    inference(instantiation,[status(thm)],[c_36825])).

cnf(c_37715,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,X0_59,sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_37069])).

cnf(c_37925,plain,
    ( ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
    | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_37715])).

cnf(c_37926,plain,
    ( v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))))) = iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37925])).

cnf(c_36661,plain,
    ( ~ r3_tsep_1(sK8,X0_58,X1_58)
    | ~ v5_pre_topc(X0_59,X1_58,X2_58)
    | ~ v5_pre_topc(X1_59,X0_58,X2_58)
    | v5_pre_topc(k10_tmap_1(sK8,X2_58,X0_58,X1_58,X1_59,X0_59),k1_tsep_1(sK8,X0_58,X1_58),X2_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X1_58),u1_struct_0(X2_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(X0_58),u1_struct_0(X2_58))
    | ~ m1_pre_topc(X1_58,sK8)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X2_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X2_58))))
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(X1_59) ),
    inference(instantiation,[status(thm)],[c_11807])).

cnf(c_37096,plain,
    ( ~ r3_tsep_1(sK8,X0_58,sK10)
    | ~ v5_pre_topc(X0_59,X0_58,X1_58)
    | ~ v5_pre_topc(X1_59,sK10,X1_58)
    | v5_pre_topc(k10_tmap_1(sK8,X1_58,X0_58,sK10,X0_59,X1_59),k1_tsep_1(sK8,X0_58,sK10),X1_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59) ),
    inference(instantiation,[status(thm)],[c_36661])).

cnf(c_37529,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ v5_pre_topc(X0_59,sK10,X0_58)
    | ~ v5_pre_topc(X1_59,sK9,X0_58)
    | v5_pre_topc(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59),k1_tsep_1(sK8,sK9,sK10),X0_58)
    | ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
    | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X1_59)
    | ~ v1_funct_1(X0_59) ),
    inference(instantiation,[status(thm)],[c_37096])).

cnf(c_37888,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | ~ v5_pre_topc(X0_59,sK9,sK5(sK8,sK9,sK10))
    | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,X0_59,sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10))
    | ~ v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10))
    | ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(X0_59)
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_37529])).

cnf(c_38267,plain,
    ( ~ r3_tsep_1(sK8,sK9,sK10)
    | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10))
    | ~ v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10))
    | ~ v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10))
    | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
    | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
    | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_37888])).

cnf(c_38268,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10)) = iProver_top
    | v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10)) != iProver_top
    | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38267])).

cnf(c_38910,plain,
    ( r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38906,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_1493,c_1506,c_1519,c_1532,c_1545,c_1558,c_1571,c_1584,c_6265,c_14809,c_14811,c_14813,c_14815,c_14819,c_26412,c_30137,c_37926,c_38268])).

cnf(c_38914,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_38834,c_38910])).

cnf(c_39035,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38914,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_6265])).

cnf(c_56,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X5,X1,X0)
    | v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_11822,plain,
    ( ~ sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
    | ~ v5_pre_topc(X1_59,X1_58,X0_58)
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,X1_59),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
    | ~ v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58))))
    | ~ v1_funct_1(X1_59) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_13248,plain,
    ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) != iProver_top
    | v5_pre_topc(X1_59,X1_58,X0_58) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,X1_59),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) = iProver_top
    | v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11822])).

cnf(c_39045,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39035,c_13248])).

cnf(c_13346,plain,
    ( ~ sP0(sK4(sK8,X0_58,X1_58),X1_58,X0_58,sK8)
    | r3_tsep_1(sK8,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X1_58,sK8)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11844])).

cnf(c_13665,plain,
    ( ~ sP0(sK4(sK8,X0_58,sK10),sK10,X0_58,sK8)
    | r3_tsep_1(sK8,X0_58,sK10)
    | ~ r1_tsep_1(X0_58,sK10)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_13346])).

cnf(c_13870,plain,
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
    inference(instantiation,[status(thm)],[c_13665])).

cnf(c_13871,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13870])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_424,plain,
    ( ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | sP0(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_22,c_21,c_20])).

cnf(c_425,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_11810,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | ~ v5_pre_topc(sK3(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_14155,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | ~ v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_11810])).

cnf(c_14159,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14155])).

cnf(c_14153,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) ),
    inference(instantiation,[status(thm)],[c_11853])).

cnf(c_14163,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14153])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11855,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_14150,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_11855])).

cnf(c_14169,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14150])).

cnf(c_14148,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_11854])).

cnf(c_14173,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14148])).

cnf(c_14146,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) ),
    inference(instantiation,[status(thm)],[c_11856])).

cnf(c_14177,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14146])).

cnf(c_39136,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39045,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_1493,c_1506,c_1519,c_1532,c_1545,c_1558,c_1571,c_1584,c_6265,c_13871,c_14159,c_14163,c_14169,c_14173,c_14177,c_14809,c_14811,c_14813,c_14815,c_14819,c_26412,c_30137,c_37926,c_38268])).

cnf(c_39141,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | sP2(sK8,sK9,sK10) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17765,c_39136])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11851,plain,
    ( sP0(X0_58,X1_58,X2_58,X3_58)
    | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),X2_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_14149,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_11851])).

cnf(c_14171,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14149])).

cnf(c_14152,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) ),
    inference(instantiation,[status(thm)],[c_11849])).

cnf(c_14165,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14152])).

cnf(c_13349,plain,
    ( r3_tsep_1(sK8,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X1_58,sK8)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ v2_pre_topc(sK8)
    | l1_pre_topc(sK4(sK8,X0_58,X1_58))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11843])).

cnf(c_13653,plain,
    ( r3_tsep_1(sK8,X0_58,sK10)
    | ~ r1_tsep_1(X0_58,sK10)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ v2_pre_topc(sK8)
    | l1_pre_topc(sK4(sK8,X0_58,sK10))
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_13349])).

cnf(c_13867,plain,
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
    inference(instantiation,[status(thm)],[c_13653])).

cnf(c_13868,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13867])).

cnf(c_13348,plain,
    ( r3_tsep_1(sK8,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X1_58,sK8)
    | ~ m1_pre_topc(X0_58,sK8)
    | v2_pre_topc(sK4(sK8,X0_58,X1_58))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11842])).

cnf(c_13643,plain,
    ( r3_tsep_1(sK8,X0_58,sK10)
    | ~ r1_tsep_1(X0_58,sK10)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ m1_pre_topc(sK10,sK8)
    | v2_pre_topc(sK4(sK8,X0_58,sK10))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK10)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_13348])).

cnf(c_13858,plain,
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
    inference(instantiation,[status(thm)],[c_13643])).

cnf(c_13859,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13858])).

cnf(c_13347,plain,
    ( r3_tsep_1(sK8,X0_58,X1_58)
    | ~ r1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X1_58,sK8)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | v2_struct_0(X1_58)
    | ~ v2_struct_0(sK4(sK8,X0_58,X1_58))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11841])).

cnf(c_13633,plain,
    ( r3_tsep_1(sK8,X0_58,sK10)
    | ~ r1_tsep_1(X0_58,sK10)
    | ~ m1_pre_topc(X0_58,sK8)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(X0_58)
    | ~ v2_struct_0(sK4(sK8,X0_58,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_13347])).

cnf(c_13855,plain,
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
    inference(instantiation,[status(thm)],[c_13633])).

cnf(c_13856,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13855])).

cnf(c_75,plain,
    ( sP2(sK8,sK9,sK10) = iProver_top
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39141,c_38910,c_14171,c_14165,c_13871,c_13868,c_13859,c_13856,c_6265,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.66/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.66/3.49  
% 23.66/3.49  ------  iProver source info
% 23.66/3.49  
% 23.66/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.66/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.66/3.49  git: non_committed_changes: false
% 23.66/3.49  git: last_make_outside_of_git: false
% 23.66/3.49  
% 23.66/3.49  ------ 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options
% 23.66/3.49  
% 23.66/3.49  --out_options                           all
% 23.66/3.49  --tptp_safe_out                         true
% 23.66/3.49  --problem_path                          ""
% 23.66/3.49  --include_path                          ""
% 23.66/3.49  --clausifier                            res/vclausify_rel
% 23.66/3.49  --clausifier_options                    ""
% 23.66/3.49  --stdin                                 false
% 23.66/3.49  --stats_out                             all
% 23.66/3.49  
% 23.66/3.49  ------ General Options
% 23.66/3.49  
% 23.66/3.49  --fof                                   false
% 23.66/3.49  --time_out_real                         305.
% 23.66/3.49  --time_out_virtual                      -1.
% 23.66/3.49  --symbol_type_check                     false
% 23.66/3.49  --clausify_out                          false
% 23.66/3.49  --sig_cnt_out                           false
% 23.66/3.49  --trig_cnt_out                          false
% 23.66/3.49  --trig_cnt_out_tolerance                1.
% 23.66/3.49  --trig_cnt_out_sk_spl                   false
% 23.66/3.49  --abstr_cl_out                          false
% 23.66/3.49  
% 23.66/3.49  ------ Global Options
% 23.66/3.49  
% 23.66/3.49  --schedule                              default
% 23.66/3.49  --add_important_lit                     false
% 23.66/3.49  --prop_solver_per_cl                    1000
% 23.66/3.49  --min_unsat_core                        false
% 23.66/3.49  --soft_assumptions                      false
% 23.66/3.49  --soft_lemma_size                       3
% 23.66/3.49  --prop_impl_unit_size                   0
% 23.66/3.49  --prop_impl_unit                        []
% 23.66/3.49  --share_sel_clauses                     true
% 23.66/3.49  --reset_solvers                         false
% 23.66/3.49  --bc_imp_inh                            [conj_cone]
% 23.66/3.49  --conj_cone_tolerance                   3.
% 23.66/3.49  --extra_neg_conj                        none
% 23.66/3.49  --large_theory_mode                     true
% 23.66/3.49  --prolific_symb_bound                   200
% 23.66/3.49  --lt_threshold                          2000
% 23.66/3.49  --clause_weak_htbl                      true
% 23.66/3.49  --gc_record_bc_elim                     false
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing Options
% 23.66/3.49  
% 23.66/3.49  --preprocessing_flag                    true
% 23.66/3.49  --time_out_prep_mult                    0.1
% 23.66/3.49  --splitting_mode                        input
% 23.66/3.49  --splitting_grd                         true
% 23.66/3.49  --splitting_cvd                         false
% 23.66/3.49  --splitting_cvd_svl                     false
% 23.66/3.49  --splitting_nvd                         32
% 23.66/3.49  --sub_typing                            true
% 23.66/3.49  --prep_gs_sim                           true
% 23.66/3.49  --prep_unflatten                        true
% 23.66/3.49  --prep_res_sim                          true
% 23.66/3.49  --prep_upred                            true
% 23.66/3.49  --prep_sem_filter                       exhaustive
% 23.66/3.49  --prep_sem_filter_out                   false
% 23.66/3.49  --pred_elim                             true
% 23.66/3.49  --res_sim_input                         true
% 23.66/3.49  --eq_ax_congr_red                       true
% 23.66/3.49  --pure_diseq_elim                       true
% 23.66/3.49  --brand_transform                       false
% 23.66/3.49  --non_eq_to_eq                          false
% 23.66/3.49  --prep_def_merge                        true
% 23.66/3.49  --prep_def_merge_prop_impl              false
% 23.66/3.49  --prep_def_merge_mbd                    true
% 23.66/3.49  --prep_def_merge_tr_red                 false
% 23.66/3.49  --prep_def_merge_tr_cl                  false
% 23.66/3.49  --smt_preprocessing                     true
% 23.66/3.49  --smt_ac_axioms                         fast
% 23.66/3.49  --preprocessed_out                      false
% 23.66/3.49  --preprocessed_stats                    false
% 23.66/3.49  
% 23.66/3.49  ------ Abstraction refinement Options
% 23.66/3.49  
% 23.66/3.49  --abstr_ref                             []
% 23.66/3.49  --abstr_ref_prep                        false
% 23.66/3.49  --abstr_ref_until_sat                   false
% 23.66/3.49  --abstr_ref_sig_restrict                funpre
% 23.66/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.49  --abstr_ref_under                       []
% 23.66/3.49  
% 23.66/3.49  ------ SAT Options
% 23.66/3.49  
% 23.66/3.49  --sat_mode                              false
% 23.66/3.49  --sat_fm_restart_options                ""
% 23.66/3.49  --sat_gr_def                            false
% 23.66/3.49  --sat_epr_types                         true
% 23.66/3.49  --sat_non_cyclic_types                  false
% 23.66/3.49  --sat_finite_models                     false
% 23.66/3.49  --sat_fm_lemmas                         false
% 23.66/3.49  --sat_fm_prep                           false
% 23.66/3.49  --sat_fm_uc_incr                        true
% 23.66/3.49  --sat_out_model                         small
% 23.66/3.49  --sat_out_clauses                       false
% 23.66/3.49  
% 23.66/3.49  ------ QBF Options
% 23.66/3.49  
% 23.66/3.49  --qbf_mode                              false
% 23.66/3.49  --qbf_elim_univ                         false
% 23.66/3.49  --qbf_dom_inst                          none
% 23.66/3.49  --qbf_dom_pre_inst                      false
% 23.66/3.49  --qbf_sk_in                             false
% 23.66/3.49  --qbf_pred_elim                         true
% 23.66/3.49  --qbf_split                             512
% 23.66/3.49  
% 23.66/3.49  ------ BMC1 Options
% 23.66/3.49  
% 23.66/3.49  --bmc1_incremental                      false
% 23.66/3.49  --bmc1_axioms                           reachable_all
% 23.66/3.49  --bmc1_min_bound                        0
% 23.66/3.49  --bmc1_max_bound                        -1
% 23.66/3.49  --bmc1_max_bound_default                -1
% 23.66/3.49  --bmc1_symbol_reachability              true
% 23.66/3.49  --bmc1_property_lemmas                  false
% 23.66/3.49  --bmc1_k_induction                      false
% 23.66/3.49  --bmc1_non_equiv_states                 false
% 23.66/3.49  --bmc1_deadlock                         false
% 23.66/3.49  --bmc1_ucm                              false
% 23.66/3.49  --bmc1_add_unsat_core                   none
% 23.66/3.49  --bmc1_unsat_core_children              false
% 23.66/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.49  --bmc1_out_stat                         full
% 23.66/3.49  --bmc1_ground_init                      false
% 23.66/3.49  --bmc1_pre_inst_next_state              false
% 23.66/3.49  --bmc1_pre_inst_state                   false
% 23.66/3.49  --bmc1_pre_inst_reach_state             false
% 23.66/3.49  --bmc1_out_unsat_core                   false
% 23.66/3.49  --bmc1_aig_witness_out                  false
% 23.66/3.49  --bmc1_verbose                          false
% 23.66/3.49  --bmc1_dump_clauses_tptp                false
% 23.66/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.49  --bmc1_dump_file                        -
% 23.66/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.49  --bmc1_ucm_extend_mode                  1
% 23.66/3.49  --bmc1_ucm_init_mode                    2
% 23.66/3.49  --bmc1_ucm_cone_mode                    none
% 23.66/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.49  --bmc1_ucm_relax_model                  4
% 23.66/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.49  --bmc1_ucm_layered_model                none
% 23.66/3.49  --bmc1_ucm_max_lemma_size               10
% 23.66/3.49  
% 23.66/3.49  ------ AIG Options
% 23.66/3.49  
% 23.66/3.49  --aig_mode                              false
% 23.66/3.49  
% 23.66/3.49  ------ Instantiation Options
% 23.66/3.49  
% 23.66/3.49  --instantiation_flag                    true
% 23.66/3.49  --inst_sos_flag                         true
% 23.66/3.49  --inst_sos_phase                        true
% 23.66/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel_side                     num_symb
% 23.66/3.49  --inst_solver_per_active                1400
% 23.66/3.49  --inst_solver_calls_frac                1.
% 23.66/3.49  --inst_passive_queue_type               priority_queues
% 23.66/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.49  --inst_passive_queues_freq              [25;2]
% 23.66/3.49  --inst_dismatching                      true
% 23.66/3.49  --inst_eager_unprocessed_to_passive     true
% 23.66/3.49  --inst_prop_sim_given                   true
% 23.66/3.49  --inst_prop_sim_new                     false
% 23.66/3.49  --inst_subs_new                         false
% 23.66/3.49  --inst_eq_res_simp                      false
% 23.66/3.49  --inst_subs_given                       false
% 23.66/3.49  --inst_orphan_elimination               true
% 23.66/3.49  --inst_learning_loop_flag               true
% 23.66/3.49  --inst_learning_start                   3000
% 23.66/3.49  --inst_learning_factor                  2
% 23.66/3.49  --inst_start_prop_sim_after_learn       3
% 23.66/3.49  --inst_sel_renew                        solver
% 23.66/3.49  --inst_lit_activity_flag                true
% 23.66/3.49  --inst_restr_to_given                   false
% 23.66/3.49  --inst_activity_threshold               500
% 23.66/3.49  --inst_out_proof                        true
% 23.66/3.49  
% 23.66/3.49  ------ Resolution Options
% 23.66/3.49  
% 23.66/3.49  --resolution_flag                       true
% 23.66/3.49  --res_lit_sel                           adaptive
% 23.66/3.49  --res_lit_sel_side                      none
% 23.66/3.49  --res_ordering                          kbo
% 23.66/3.49  --res_to_prop_solver                    active
% 23.66/3.49  --res_prop_simpl_new                    false
% 23.66/3.49  --res_prop_simpl_given                  true
% 23.66/3.49  --res_passive_queue_type                priority_queues
% 23.66/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.49  --res_passive_queues_freq               [15;5]
% 23.66/3.49  --res_forward_subs                      full
% 23.66/3.49  --res_backward_subs                     full
% 23.66/3.49  --res_forward_subs_resolution           true
% 23.66/3.49  --res_backward_subs_resolution          true
% 23.66/3.49  --res_orphan_elimination                true
% 23.66/3.49  --res_time_limit                        2.
% 23.66/3.49  --res_out_proof                         true
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Options
% 23.66/3.49  
% 23.66/3.49  --superposition_flag                    true
% 23.66/3.49  --sup_passive_queue_type                priority_queues
% 23.66/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.49  --demod_completeness_check              fast
% 23.66/3.49  --demod_use_ground                      true
% 23.66/3.49  --sup_to_prop_solver                    passive
% 23.66/3.49  --sup_prop_simpl_new                    true
% 23.66/3.49  --sup_prop_simpl_given                  true
% 23.66/3.49  --sup_fun_splitting                     true
% 23.66/3.49  --sup_smt_interval                      50000
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Simplification Setup
% 23.66/3.49  
% 23.66/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.66/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_immed_triv                        [TrivRules]
% 23.66/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_bw_main                     []
% 23.66/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_input_bw                          []
% 23.66/3.49  
% 23.66/3.49  ------ Combination Options
% 23.66/3.49  
% 23.66/3.49  --comb_res_mult                         3
% 23.66/3.49  --comb_sup_mult                         2
% 23.66/3.49  --comb_inst_mult                        10
% 23.66/3.49  
% 23.66/3.49  ------ Debug Options
% 23.66/3.49  
% 23.66/3.49  --dbg_backtrace                         false
% 23.66/3.49  --dbg_dump_prop_clauses                 false
% 23.66/3.49  --dbg_dump_prop_clauses_file            -
% 23.66/3.49  --dbg_out_stat                          false
% 23.66/3.49  ------ Parsing...
% 23.66/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.66/3.49  ------ Proving...
% 23.66/3.49  ------ Problem Properties 
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  clauses                                 62
% 23.66/3.49  conjectures                             9
% 23.66/3.49  EPR                                     12
% 23.66/3.49  Horn                                    20
% 23.66/3.49  unary                                   7
% 23.66/3.49  binary                                  19
% 23.66/3.49  lits                                    454
% 23.66/3.49  lits eq                                 3
% 23.66/3.49  fd_pure                                 0
% 23.66/3.49  fd_pseudo                               0
% 23.66/3.49  fd_cond                                 0
% 23.66/3.49  fd_pseudo_cond                          3
% 23.66/3.49  AC symbols                              0
% 23.66/3.49  
% 23.66/3.49  ------ Schedule dynamic 5 is on 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  ------ 
% 23.66/3.49  Current options:
% 23.66/3.49  ------ 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options
% 23.66/3.49  
% 23.66/3.49  --out_options                           all
% 23.66/3.49  --tptp_safe_out                         true
% 23.66/3.49  --problem_path                          ""
% 23.66/3.49  --include_path                          ""
% 23.66/3.49  --clausifier                            res/vclausify_rel
% 23.66/3.49  --clausifier_options                    ""
% 23.66/3.49  --stdin                                 false
% 23.66/3.49  --stats_out                             all
% 23.66/3.49  
% 23.66/3.49  ------ General Options
% 23.66/3.49  
% 23.66/3.49  --fof                                   false
% 23.66/3.49  --time_out_real                         305.
% 23.66/3.49  --time_out_virtual                      -1.
% 23.66/3.49  --symbol_type_check                     false
% 23.66/3.49  --clausify_out                          false
% 23.66/3.49  --sig_cnt_out                           false
% 23.66/3.49  --trig_cnt_out                          false
% 23.66/3.49  --trig_cnt_out_tolerance                1.
% 23.66/3.49  --trig_cnt_out_sk_spl                   false
% 23.66/3.49  --abstr_cl_out                          false
% 23.66/3.49  
% 23.66/3.49  ------ Global Options
% 23.66/3.49  
% 23.66/3.49  --schedule                              default
% 23.66/3.49  --add_important_lit                     false
% 23.66/3.49  --prop_solver_per_cl                    1000
% 23.66/3.49  --min_unsat_core                        false
% 23.66/3.49  --soft_assumptions                      false
% 23.66/3.49  --soft_lemma_size                       3
% 23.66/3.49  --prop_impl_unit_size                   0
% 23.66/3.49  --prop_impl_unit                        []
% 23.66/3.49  --share_sel_clauses                     true
% 23.66/3.49  --reset_solvers                         false
% 23.66/3.49  --bc_imp_inh                            [conj_cone]
% 23.66/3.49  --conj_cone_tolerance                   3.
% 23.66/3.49  --extra_neg_conj                        none
% 23.66/3.49  --large_theory_mode                     true
% 23.66/3.49  --prolific_symb_bound                   200
% 23.66/3.49  --lt_threshold                          2000
% 23.66/3.49  --clause_weak_htbl                      true
% 23.66/3.49  --gc_record_bc_elim                     false
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing Options
% 23.66/3.49  
% 23.66/3.49  --preprocessing_flag                    true
% 23.66/3.49  --time_out_prep_mult                    0.1
% 23.66/3.49  --splitting_mode                        input
% 23.66/3.49  --splitting_grd                         true
% 23.66/3.49  --splitting_cvd                         false
% 23.66/3.49  --splitting_cvd_svl                     false
% 23.66/3.49  --splitting_nvd                         32
% 23.66/3.49  --sub_typing                            true
% 23.66/3.49  --prep_gs_sim                           true
% 23.66/3.49  --prep_unflatten                        true
% 23.66/3.49  --prep_res_sim                          true
% 23.66/3.49  --prep_upred                            true
% 23.66/3.49  --prep_sem_filter                       exhaustive
% 23.66/3.49  --prep_sem_filter_out                   false
% 23.66/3.49  --pred_elim                             true
% 23.66/3.49  --res_sim_input                         true
% 23.66/3.49  --eq_ax_congr_red                       true
% 23.66/3.49  --pure_diseq_elim                       true
% 23.66/3.49  --brand_transform                       false
% 23.66/3.49  --non_eq_to_eq                          false
% 23.66/3.49  --prep_def_merge                        true
% 23.66/3.49  --prep_def_merge_prop_impl              false
% 23.66/3.49  --prep_def_merge_mbd                    true
% 23.66/3.49  --prep_def_merge_tr_red                 false
% 23.66/3.49  --prep_def_merge_tr_cl                  false
% 23.66/3.49  --smt_preprocessing                     true
% 23.66/3.49  --smt_ac_axioms                         fast
% 23.66/3.49  --preprocessed_out                      false
% 23.66/3.49  --preprocessed_stats                    false
% 23.66/3.49  
% 23.66/3.49  ------ Abstraction refinement Options
% 23.66/3.49  
% 23.66/3.49  --abstr_ref                             []
% 23.66/3.49  --abstr_ref_prep                        false
% 23.66/3.49  --abstr_ref_until_sat                   false
% 23.66/3.49  --abstr_ref_sig_restrict                funpre
% 23.66/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.49  --abstr_ref_under                       []
% 23.66/3.49  
% 23.66/3.49  ------ SAT Options
% 23.66/3.49  
% 23.66/3.49  --sat_mode                              false
% 23.66/3.49  --sat_fm_restart_options                ""
% 23.66/3.49  --sat_gr_def                            false
% 23.66/3.49  --sat_epr_types                         true
% 23.66/3.49  --sat_non_cyclic_types                  false
% 23.66/3.49  --sat_finite_models                     false
% 23.66/3.49  --sat_fm_lemmas                         false
% 23.66/3.49  --sat_fm_prep                           false
% 23.66/3.49  --sat_fm_uc_incr                        true
% 23.66/3.49  --sat_out_model                         small
% 23.66/3.49  --sat_out_clauses                       false
% 23.66/3.49  
% 23.66/3.49  ------ QBF Options
% 23.66/3.49  
% 23.66/3.49  --qbf_mode                              false
% 23.66/3.49  --qbf_elim_univ                         false
% 23.66/3.49  --qbf_dom_inst                          none
% 23.66/3.49  --qbf_dom_pre_inst                      false
% 23.66/3.49  --qbf_sk_in                             false
% 23.66/3.49  --qbf_pred_elim                         true
% 23.66/3.49  --qbf_split                             512
% 23.66/3.49  
% 23.66/3.49  ------ BMC1 Options
% 23.66/3.49  
% 23.66/3.49  --bmc1_incremental                      false
% 23.66/3.49  --bmc1_axioms                           reachable_all
% 23.66/3.49  --bmc1_min_bound                        0
% 23.66/3.49  --bmc1_max_bound                        -1
% 23.66/3.49  --bmc1_max_bound_default                -1
% 23.66/3.49  --bmc1_symbol_reachability              true
% 23.66/3.49  --bmc1_property_lemmas                  false
% 23.66/3.49  --bmc1_k_induction                      false
% 23.66/3.49  --bmc1_non_equiv_states                 false
% 23.66/3.49  --bmc1_deadlock                         false
% 23.66/3.49  --bmc1_ucm                              false
% 23.66/3.49  --bmc1_add_unsat_core                   none
% 23.66/3.49  --bmc1_unsat_core_children              false
% 23.66/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.49  --bmc1_out_stat                         full
% 23.66/3.49  --bmc1_ground_init                      false
% 23.66/3.49  --bmc1_pre_inst_next_state              false
% 23.66/3.49  --bmc1_pre_inst_state                   false
% 23.66/3.49  --bmc1_pre_inst_reach_state             false
% 23.66/3.49  --bmc1_out_unsat_core                   false
% 23.66/3.49  --bmc1_aig_witness_out                  false
% 23.66/3.49  --bmc1_verbose                          false
% 23.66/3.49  --bmc1_dump_clauses_tptp                false
% 23.66/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.49  --bmc1_dump_file                        -
% 23.66/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.49  --bmc1_ucm_extend_mode                  1
% 23.66/3.49  --bmc1_ucm_init_mode                    2
% 23.66/3.49  --bmc1_ucm_cone_mode                    none
% 23.66/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.49  --bmc1_ucm_relax_model                  4
% 23.66/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.49  --bmc1_ucm_layered_model                none
% 23.66/3.49  --bmc1_ucm_max_lemma_size               10
% 23.66/3.49  
% 23.66/3.49  ------ AIG Options
% 23.66/3.49  
% 23.66/3.49  --aig_mode                              false
% 23.66/3.49  
% 23.66/3.49  ------ Instantiation Options
% 23.66/3.49  
% 23.66/3.49  --instantiation_flag                    true
% 23.66/3.49  --inst_sos_flag                         true
% 23.66/3.49  --inst_sos_phase                        true
% 23.66/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel_side                     none
% 23.66/3.49  --inst_solver_per_active                1400
% 23.66/3.49  --inst_solver_calls_frac                1.
% 23.66/3.49  --inst_passive_queue_type               priority_queues
% 23.66/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.49  --inst_passive_queues_freq              [25;2]
% 23.66/3.49  --inst_dismatching                      true
% 23.66/3.49  --inst_eager_unprocessed_to_passive     true
% 23.66/3.49  --inst_prop_sim_given                   true
% 23.66/3.49  --inst_prop_sim_new                     false
% 23.66/3.49  --inst_subs_new                         false
% 23.66/3.49  --inst_eq_res_simp                      false
% 23.66/3.49  --inst_subs_given                       false
% 23.66/3.49  --inst_orphan_elimination               true
% 23.66/3.49  --inst_learning_loop_flag               true
% 23.66/3.49  --inst_learning_start                   3000
% 23.66/3.49  --inst_learning_factor                  2
% 23.66/3.49  --inst_start_prop_sim_after_learn       3
% 23.66/3.49  --inst_sel_renew                        solver
% 23.66/3.49  --inst_lit_activity_flag                true
% 23.66/3.49  --inst_restr_to_given                   false
% 23.66/3.49  --inst_activity_threshold               500
% 23.66/3.49  --inst_out_proof                        true
% 23.66/3.49  
% 23.66/3.49  ------ Resolution Options
% 23.66/3.49  
% 23.66/3.49  --resolution_flag                       false
% 23.66/3.49  --res_lit_sel                           adaptive
% 23.66/3.49  --res_lit_sel_side                      none
% 23.66/3.49  --res_ordering                          kbo
% 23.66/3.49  --res_to_prop_solver                    active
% 23.66/3.49  --res_prop_simpl_new                    false
% 23.66/3.49  --res_prop_simpl_given                  true
% 23.66/3.49  --res_passive_queue_type                priority_queues
% 23.66/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.49  --res_passive_queues_freq               [15;5]
% 23.66/3.49  --res_forward_subs                      full
% 23.66/3.49  --res_backward_subs                     full
% 23.66/3.49  --res_forward_subs_resolution           true
% 23.66/3.49  --res_backward_subs_resolution          true
% 23.66/3.49  --res_orphan_elimination                true
% 23.66/3.49  --res_time_limit                        2.
% 23.66/3.49  --res_out_proof                         true
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Options
% 23.66/3.49  
% 23.66/3.49  --superposition_flag                    true
% 23.66/3.49  --sup_passive_queue_type                priority_queues
% 23.66/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.49  --demod_completeness_check              fast
% 23.66/3.49  --demod_use_ground                      true
% 23.66/3.49  --sup_to_prop_solver                    passive
% 23.66/3.49  --sup_prop_simpl_new                    true
% 23.66/3.49  --sup_prop_simpl_given                  true
% 23.66/3.49  --sup_fun_splitting                     true
% 23.66/3.49  --sup_smt_interval                      50000
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Simplification Setup
% 23.66/3.49  
% 23.66/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.66/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_immed_triv                        [TrivRules]
% 23.66/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_bw_main                     []
% 23.66/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_input_bw                          []
% 23.66/3.49  
% 23.66/3.49  ------ Combination Options
% 23.66/3.49  
% 23.66/3.49  --comb_res_mult                         3
% 23.66/3.49  --comb_sup_mult                         2
% 23.66/3.49  --comb_inst_mult                        10
% 23.66/3.49  
% 23.66/3.49  ------ Debug Options
% 23.66/3.49  
% 23.66/3.49  --dbg_backtrace                         false
% 23.66/3.49  --dbg_dump_prop_clauses                 false
% 23.66/3.49  --dbg_dump_prop_clauses_file            -
% 23.66/3.49  --dbg_out_stat                          false
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  ------ Proving...
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  % SZS status Theorem for theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  fof(f23,plain,(
% 23.66/3.49    ! [X3,X2,X1,X0] : (sP0(X3,X2,X1,X0) <=> ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)))),
% 23.66/3.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 23.66/3.49  
% 23.66/3.49  fof(f31,plain,(
% 23.66/3.49    ! [X3,X2,X1,X0] : ((sP0(X3,X2,X1,X0) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~sP0(X3,X2,X1,X0)))),
% 23.66/3.49    inference(nnf_transformation,[],[f23])).
% 23.66/3.49  
% 23.66/3.49  fof(f32,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 23.66/3.49    inference(rectify,[],[f31])).
% 23.66/3.49  
% 23.66/3.49  fof(f33,plain,(
% 23.66/3.49    ! [X3,X2,X1,X0] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) => ((~m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(sK3(X0,X1,X2,X3))))),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f34,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(sK3(X0,X1,X2,X3)))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 23.66/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 23.66/3.49  
% 23.66/3.49  fof(f77,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f79,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f26,plain,(
% 23.66/3.49    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> (! [X3] : (! [X4] : (sP1(X3,X2,X1,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)))),
% 23.66/3.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 23.66/3.49  
% 23.66/3.49  fof(f42,plain,(
% 23.66/3.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (! [X4] : (sP1(X3,X2,X1,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 23.66/3.49    inference(nnf_transformation,[],[f26])).
% 23.66/3.49  
% 23.66/3.49  fof(f43,plain,(
% 23.66/3.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (! [X4] : (sP1(X3,X2,X1,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 23.66/3.49    inference(flattening,[],[f42])).
% 23.66/3.49  
% 23.66/3.49  fof(f44,plain,(
% 23.66/3.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X5] : (! [X6] : (sP1(X5,X2,X1,X0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(X6,X1,X5) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 23.66/3.49    inference(rectify,[],[f43])).
% 23.66/3.49  
% 23.66/3.49  fof(f46,plain,(
% 23.66/3.49    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => (~sP1(X3,X2,X1,X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(sK6(X0,X1,X2),X1,X3) & v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(sK6(X0,X1,X2))))) )),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f45,plain,(
% 23.66/3.49    ! [X2,X1,X0] : (? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (? [X4] : (~sP1(sK5(X0,X1,X2),X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) & v5_pre_topc(X4,X1,sK5(X0,X1,X2)) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) & v1_funct_1(X4)) & l1_pre_topc(sK5(X0,X1,X2)) & v2_pre_topc(sK5(X0,X1,X2)) & ~v2_struct_0(sK5(X0,X1,X2))))),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f47,plain,(
% 23.66/3.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) & v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2)) & v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) & v1_funct_1(sK6(X0,X1,X2))) & l1_pre_topc(sK5(X0,X1,X2)) & v2_pre_topc(sK5(X0,X1,X2)) & ~v2_struct_0(sK5(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) & ((! [X5] : (! [X6] : (sP1(X5,X2,X1,X0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(X6,X1,X5) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 23.66/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f46,f45])).
% 23.66/3.49  
% 23.66/3.49  fof(f99,plain,(
% 23.66/3.49    ( ! [X6,X2,X0,X5,X1] : (sP1(X5,X2,X1,X0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(X6,X1,X5) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~sP2(X0,X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f73,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(sK3(X0,X1,X2,X3))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f74,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f76,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f80,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f75,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f81,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f1,axiom,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f9,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.66/3.49    inference(ennf_transformation,[],[f1])).
% 23.66/3.49  
% 23.66/3.49  fof(f10,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.66/3.49    inference(flattening,[],[f9])).
% 23.66/3.49  
% 23.66/3.49  fof(f28,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.66/3.49    inference(nnf_transformation,[],[f10])).
% 23.66/3.49  
% 23.66/3.49  fof(f59,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f28])).
% 23.66/3.49  
% 23.66/3.49  fof(f126,plain,(
% 23.66/3.49    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 23.66/3.49    inference(equality_resolution,[],[f59])).
% 23.66/3.49  
% 23.66/3.49  fof(f83,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f2,axiom,(
% 23.66/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r1_tsep_1(X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f11,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6))) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f2])).
% 23.66/3.49  
% 23.66/3.49  fof(f12,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f11])).
% 23.66/3.49  
% 23.66/3.49  fof(f29,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(nnf_transformation,[],[f12])).
% 23.66/3.49  
% 23.66/3.49  fof(f30,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f29])).
% 23.66/3.49  
% 23.66/3.49  fof(f64,plain,(
% 23.66/3.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r1_tsep_1(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f30])).
% 23.66/3.49  
% 23.66/3.49  fof(f4,axiom,(
% 23.66/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2))))))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f15,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f4])).
% 23.66/3.49  
% 23.66/3.49  fof(f16,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f15])).
% 23.66/3.49  
% 23.66/3.49  fof(f24,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(definition_folding,[],[f16,f23])).
% 23.66/3.49  
% 23.66/3.49  fof(f35,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | (? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(nnf_transformation,[],[f24])).
% 23.66/3.49  
% 23.66/3.49  fof(f36,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | ? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f35])).
% 23.66/3.49  
% 23.66/3.49  fof(f37,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | ? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X4] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(rectify,[],[f36])).
% 23.66/3.49  
% 23.66/3.49  fof(f38,plain,(
% 23.66/3.49    ! [X2,X1,X0] : (? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (~sP0(sK4(X0,X1,X2),X2,X1,X0) & l1_pre_topc(sK4(X0,X1,X2)) & v2_pre_topc(sK4(X0,X1,X2)) & ~v2_struct_0(sK4(X0,X1,X2))))),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f39,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | (~sP0(sK4(X0,X1,X2),X2,X1,X0) & l1_pre_topc(sK4(X0,X1,X2)) & v2_pre_topc(sK4(X0,X1,X2)) & ~v2_struct_0(sK4(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) & ((! [X4] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 23.66/3.49  
% 23.66/3.49  fof(f90,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | ~sP0(sK4(X0,X1,X2),X2,X1,X0) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f39])).
% 23.66/3.49  
% 23.66/3.49  fof(f89,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | l1_pre_topc(sK4(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f39])).
% 23.66/3.49  
% 23.66/3.49  fof(f88,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | v2_pre_topc(sK4(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f39])).
% 23.66/3.49  
% 23.66/3.49  fof(f87,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | ~v2_struct_0(sK4(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f39])).
% 23.66/3.49  
% 23.66/3.49  fof(f106,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f25,plain,(
% 23.66/3.49    ! [X3,X2,X1,X0,X4] : (sP1(X3,X2,X1,X0,X4) <=> ! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)))),
% 23.66/3.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 23.66/3.49  
% 23.66/3.49  fof(f48,plain,(
% 23.66/3.49    ! [X3,X2,X1,X0,X4] : ((sP1(X3,X2,X1,X0,X4) | ? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~sP1(X3,X2,X1,X0,X4)))),
% 23.66/3.49    inference(nnf_transformation,[],[f25])).
% 23.66/3.49  
% 23.66/3.49  fof(f49,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X5,X1,X0) & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X5))) & (! [X6] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6)) | ~sP1(X0,X1,X2,X3,X4)))),
% 23.66/3.49    inference(rectify,[],[f48])).
% 23.66/3.49  
% 23.66/3.49  fof(f50,plain,(
% 23.66/3.49    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X5,X1,X0) & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)))) & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) & v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7(X0,X1,X2,X3,X4))))),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f51,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)))) & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) & v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7(X0,X1,X2,X3,X4)))) & (! [X6] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6)) | ~sP1(X0,X1,X2,X3,X4)))),
% 23.66/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f49,f50])).
% 23.66/3.49  
% 23.66/3.49  fof(f115,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f51])).
% 23.66/3.49  
% 23.66/3.49  fof(f3,axiom,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f13,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f3])).
% 23.66/3.49  
% 23.66/3.49  fof(f14,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f13])).
% 23.66/3.49  
% 23.66/3.49  fof(f66,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f14])).
% 23.66/3.49  
% 23.66/3.49  fof(f113,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f51])).
% 23.66/3.49  
% 23.66/3.49  fof(f112,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | v1_funct_1(sK7(X0,X1,X2,X3,X4))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f51])).
% 23.66/3.49  
% 23.66/3.49  fof(f6,axiom,(
% 23.66/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)))))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f19,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f6])).
% 23.66/3.49  
% 23.66/3.49  fof(f20,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f19])).
% 23.66/3.49  
% 23.66/3.49  fof(f40,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | (~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(nnf_transformation,[],[f20])).
% 23.66/3.49  
% 23.66/3.49  fof(f41,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | ~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f40])).
% 23.66/3.49  
% 23.66/3.49  fof(f97,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f41])).
% 23.66/3.49  
% 23.66/3.49  fof(f5,axiom,(
% 23.66/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f17,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f5])).
% 23.66/3.49  
% 23.66/3.49  fof(f18,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f17])).
% 23.66/3.49  
% 23.66/3.49  fof(f93,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f18])).
% 23.66/3.49  
% 23.66/3.49  fof(f96,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f41])).
% 23.66/3.49  
% 23.66/3.49  fof(f67,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f14])).
% 23.66/3.49  
% 23.66/3.49  fof(f68,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f14])).
% 23.66/3.49  
% 23.66/3.49  fof(f116,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f51])).
% 23.66/3.49  
% 23.66/3.49  fof(f114,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f51])).
% 23.66/3.49  
% 23.66/3.49  fof(f105,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f104,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f103,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v1_funct_1(sK6(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f102,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | l1_pre_topc(sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f101,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v2_pre_topc(sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f100,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~v2_struct_0(sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f107,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f7,conjecture,(
% 23.66/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 23.66/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f8,negated_conjecture,(
% 23.66/3.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 23.66/3.49    inference(negated_conjecture,[],[f7])).
% 23.66/3.49  
% 23.66/3.49  fof(f21,plain,(
% 23.66/3.49    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f8])).
% 23.66/3.49  
% 23.66/3.49  fof(f22,plain,(
% 23.66/3.49    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f21])).
% 23.66/3.49  
% 23.66/3.49  fof(f27,plain,(
% 23.66/3.49    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> sP2(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.66/3.49    inference(definition_folding,[],[f22,f26,f25])).
% 23.66/3.49  
% 23.66/3.49  fof(f52,plain,(
% 23.66/3.49    ? [X0] : (? [X1] : (? [X2] : (((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.66/3.49    inference(nnf_transformation,[],[f27])).
% 23.66/3.49  
% 23.66/3.49  fof(f53,plain,(
% 23.66/3.49    ? [X0] : (? [X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.66/3.49    inference(flattening,[],[f52])).
% 23.66/3.49  
% 23.66/3.49  fof(f56,plain,(
% 23.66/3.49    ( ! [X0,X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((~sP2(X0,X1,sK10) | ~r3_tsep_1(X0,X1,sK10)) & (sP2(X0,X1,sK10) | r3_tsep_1(X0,X1,sK10)) & m1_pre_topc(sK10,X0) & ~v2_struct_0(sK10))) )),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f55,plain,(
% 23.66/3.49    ( ! [X0] : (? [X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~sP2(X0,sK9,X2) | ~r3_tsep_1(X0,sK9,X2)) & (sP2(X0,sK9,X2) | r3_tsep_1(X0,sK9,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK9,X0) & ~v2_struct_0(sK9))) )),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f54,plain,(
% 23.66/3.49    ? [X0] : (? [X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~sP2(sK8,X1,X2) | ~r3_tsep_1(sK8,X1,X2)) & (sP2(sK8,X1,X2) | r3_tsep_1(sK8,X1,X2)) & m1_pre_topc(X2,sK8) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK8) & ~v2_struct_0(X1)) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8))),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f57,plain,(
% 23.66/3.49    (((~sP2(sK8,sK9,sK10) | ~r3_tsep_1(sK8,sK9,sK10)) & (sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10)) & m1_pre_topc(sK10,sK8) & ~v2_struct_0(sK10)) & m1_pre_topc(sK9,sK8) & ~v2_struct_0(sK9)) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8)),
% 23.66/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f53,f56,f55,f54])).
% 23.66/3.49  
% 23.66/3.49  fof(f125,plain,(
% 23.66/3.49    ~sP2(sK8,sK9,sK10) | ~r3_tsep_1(sK8,sK9,sK10)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f117,plain,(
% 23.66/3.49    ~v2_struct_0(sK8)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f118,plain,(
% 23.66/3.49    v2_pre_topc(sK8)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f119,plain,(
% 23.66/3.49    l1_pre_topc(sK8)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f120,plain,(
% 23.66/3.49    ~v2_struct_0(sK9)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f121,plain,(
% 23.66/3.49    m1_pre_topc(sK9,sK8)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f122,plain,(
% 23.66/3.49    ~v2_struct_0(sK10)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f123,plain,(
% 23.66/3.49    m1_pre_topc(sK10,sK8)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f85,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f39])).
% 23.66/3.49  
% 23.66/3.49  fof(f124,plain,(
% 23.66/3.49    sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10)),
% 23.66/3.49    inference(cnf_transformation,[],[f57])).
% 23.66/3.49  
% 23.66/3.49  fof(f98,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~sP2(X0,X1,X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f47])).
% 23.66/3.49  
% 23.66/3.49  fof(f110,plain,(
% 23.66/3.49    ( ! [X6,X4,X2,X0,X3,X1] : (v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6) | ~sP1(X0,X1,X2,X3,X4)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f51])).
% 23.66/3.49  
% 23.66/3.49  fof(f84,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK3(X0,X1,X2,X3))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f82,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f78,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  cnf(c_18,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f77]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11850,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_18]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13220,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11850]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_16,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f79]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11852,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_16]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13218,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11852]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_48,plain,
% 23.66/3.49      ( sP1(X0,X1,X2,X3,X4)
% 23.66/3.49      | ~ sP2(X3,X2,X1)
% 23.66/3.49      | ~ v5_pre_topc(X4,X2,X0)
% 23.66/3.49      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
% 23.66/3.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
% 23.66/3.49      | ~ v2_pre_topc(X0)
% 23.66/3.49      | ~ l1_pre_topc(X0)
% 23.66/3.49      | v2_struct_0(X0)
% 23.66/3.49      | ~ v1_funct_1(X4) ),
% 23.66/3.49      inference(cnf_transformation,[],[f99]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11830,plain,
% 23.66/3.49      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.49      | ~ sP2(X3_58,X2_58,X1_58)
% 23.66/3.49      | ~ v5_pre_topc(X0_59,X2_58,X0_58)
% 23.66/3.49      | ~ v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58))
% 23.66/3.49      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58))))
% 23.66/3.49      | ~ v2_pre_topc(X0_58)
% 23.66/3.49      | ~ l1_pre_topc(X0_58)
% 23.66/3.49      | v2_struct_0(X0_58)
% 23.66/3.49      | ~ v1_funct_1(X0_59) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_48]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13240,plain,
% 23.66/3.49      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.49      | sP2(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.49      | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
% 23.66/3.49      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.49      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(X0_59) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11830]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_16983,plain,
% 23.66/3.49      ( sP1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) = iProver_top
% 23.66/3.49      | sP0(X0_58,X5_58,X2_58,X4_58) = iProver_top
% 23.66/3.49      | sP2(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.49      | v5_pre_topc(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),X2_58,X0_58) != iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13218,c_13240]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_17765,plain,
% 23.66/3.49      ( sP1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) = iProver_top
% 23.66/3.49      | sP0(X0_58,X5_58,X2_58,X4_58) = iProver_top
% 23.66/3.49      | sP2(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.49      | v5_pre_topc(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58)),X2_58,X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X4_58,X0_58,k1_tsep_1(X4_58,X2_58,X5_58),X2_58,sK3(X0_58,X5_58,X2_58,X4_58))) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13220,c_16983]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_22,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3) | v1_funct_1(sK3(X0,X1,X2,X3)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f73]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11846,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | v1_funct_1(sK3(X0_58,X1_58,X2_58,X3_58)) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_22]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13224,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X0_58,X1_58,X2_58,X3_58)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11846]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_21,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11847,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | v1_funct_2(sK3(X0_58,X1_58,X2_58,X3_58),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_21]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13223,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X0_58,X1_58,X2_58,X3_58),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11847]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_19,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11849,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_19]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13221,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11849]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_15,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11853,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_15]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13217,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11853]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_20,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f75]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11848,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | m1_subset_1(sK3(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_20]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13222,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X0_58,X1_58,X2_58,X3_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11848]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_14,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11854,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_14]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13216,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11854]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_0,plain,
% 23.66/3.49      ( r2_funct_2(X0,X1,X2,X2)
% 23.66/3.49      | ~ v1_funct_2(X2,X0,X1)
% 23.66/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | ~ v1_funct_1(X2) ),
% 23.66/3.49      inference(cnf_transformation,[],[f126]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11867,plain,
% 23.66/3.49      ( r2_funct_2(X0_60,X1_60,X0_59,X0_59)
% 23.66/3.49      | ~ v1_funct_2(X0_59,X0_60,X1_60)
% 23.66/3.49      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 23.66/3.49      | ~ v1_funct_1(X0_59) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_0]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13203,plain,
% 23.66/3.49      ( r2_funct_2(X0_60,X1_60,X0_59,X0_59) = iProver_top
% 23.66/3.49      | v1_funct_2(X0_59,X0_60,X1_60) != iProver_top
% 23.66/3.49      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60))) != iProver_top
% 23.66/3.49      | v1_funct_1(X0_59) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11867]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_16040,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13218,c_13203]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11922,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X2_58),u1_struct_0(X0_58)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11850]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11923,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11849]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_17408,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_16040,c_11922,c_11923]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_12,plain,
% 23.66/3.49      ( sP0(X0,X1,X2,X3)
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f83]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11856,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_12]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13214,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11856]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_15878,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X1_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13214,c_13203]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11918,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11854]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11919,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11853]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_17397,plain,
% 23.66/3.49      ( sP0(X0_58,X1_58,X2_58,X3_58) = iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X1_58),u1_struct_0(X0_58),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58))) = iProver_top ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_15878,c_11918,c_11919]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_3,plain,
% 23.66/3.49      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 23.66/3.49      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X6)
% 23.66/3.49      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 23.66/3.49      | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
% 23.66/3.49      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 23.66/3.49      | ~ r1_tsep_1(X3,X0)
% 23.66/3.49      | ~ m1_pre_topc(X0,X2)
% 23.66/3.49      | ~ m1_pre_topc(X3,X2)
% 23.66/3.49      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 23.66/3.49      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 23.66/3.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 23.66/3.49      | ~ v2_pre_topc(X1)
% 23.66/3.49      | ~ v2_pre_topc(X2)
% 23.66/3.49      | ~ l1_pre_topc(X1)
% 23.66/3.49      | ~ l1_pre_topc(X2)
% 23.66/3.49      | v2_struct_0(X2)
% 23.66/3.49      | v2_struct_0(X1)
% 23.66/3.49      | v2_struct_0(X3)
% 23.66/3.49      | v2_struct_0(X0)
% 23.66/3.49      | ~ v1_funct_1(X4)
% 23.66/3.49      | ~ v1_funct_1(X5)
% 23.66/3.49      | ~ v1_funct_1(X6)
% 23.66/3.49      | k10_tmap_1(X2,X1,X3,X0,X6,X5) = X4 ),
% 23.66/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11864,plain,
% 23.66/3.49      ( ~ r2_funct_2(u1_struct_0(X0_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,k1_tsep_1(X2_58,X3_58,X0_58),X0_58,X0_59),X1_59)
% 23.66/3.49      | ~ r2_funct_2(u1_struct_0(X3_58),u1_struct_0(X1_58),k3_tmap_1(X2_58,X1_58,k1_tsep_1(X2_58,X3_58,X0_58),X3_58,X0_59),X2_59)
% 23.66/3.49      | ~ v1_funct_2(X1_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.49      | ~ v1_funct_2(X2_59,u1_struct_0(X3_58),u1_struct_0(X1_58))
% 23.66/3.49      | ~ v1_funct_2(X0_59,u1_struct_0(k1_tsep_1(X2_58,X3_58,X0_58)),u1_struct_0(X1_58))
% 23.66/3.49      | ~ r1_tsep_1(X3_58,X0_58)
% 23.66/3.49      | ~ m1_pre_topc(X3_58,X2_58)
% 23.66/3.49      | ~ m1_pre_topc(X0_58,X2_58)
% 23.66/3.49      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.49      | ~ m1_subset_1(X2_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58))))
% 23.66/3.49      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_58,X3_58,X0_58)),u1_struct_0(X1_58))))
% 23.66/3.49      | ~ v2_pre_topc(X2_58)
% 23.66/3.49      | ~ v2_pre_topc(X1_58)
% 23.66/3.49      | ~ l1_pre_topc(X2_58)
% 23.66/3.49      | ~ l1_pre_topc(X1_58)
% 23.66/3.49      | v2_struct_0(X0_58)
% 23.66/3.49      | v2_struct_0(X1_58)
% 23.66/3.49      | v2_struct_0(X2_58)
% 23.66/3.49      | v2_struct_0(X3_58)
% 23.66/3.49      | ~ v1_funct_1(X0_59)
% 23.66/3.49      | ~ v1_funct_1(X1_59)
% 23.66/3.49      | ~ v1_funct_1(X2_59)
% 23.66/3.49      | k10_tmap_1(X2_58,X1_58,X3_58,X0_58,X2_59,X1_59) = X0_59 ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_3]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13206,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,X1_59) = X2_59
% 23.66/3.49      | r2_funct_2(u1_struct_0(X3_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,X2_59),X1_59) != iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,X2_59),X0_59) != iProver_top
% 23.66/3.49      | v1_funct_2(X1_59,u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(X2_59,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | m1_subset_1(X2_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v1_funct_1(X2_59) != iProver_top
% 23.66/3.49      | v1_funct_1(X1_59) != iProver_top
% 23.66/3.49      | v1_funct_1(X0_59) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_11864]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_17403,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),X0_59) != iProver_top
% 23.66/3.49      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_17397,c_13206]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_19370,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,X0_59,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | r2_funct_2(u1_struct_0(X2_58),u1_struct_0(X1_58),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),X0_59) != iProver_top
% 23.66/3.49      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13214,c_17403]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_28392,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_17408,c_19370]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38536,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X3_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13218,c_28392]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38553,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13216,c_38536]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38556,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | m1_subset_1(sK3(X1_58,X3_58,X2_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13220,c_38553]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38580,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13222,c_38556]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38584,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58))) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13217,c_38580]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38625,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | v1_funct_2(sK3(X1_58,X3_58,X2_58,X0_58),u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58)),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13221,c_38584]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38769,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.49      | v1_funct_1(sK3(X1_58,X3_58,X2_58,X0_58)) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13223,c_38625]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_38772,plain,
% 23.66/3.49      ( k10_tmap_1(X0_58,X1_58,X2_58,X3_58,k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X2_58,sK3(X1_58,X3_58,X2_58,X0_58)),k3_tmap_1(X0_58,X1_58,k1_tsep_1(X0_58,X2_58,X3_58),X3_58,sK3(X1_58,X3_58,X2_58,X0_58))) = sK3(X1_58,X3_58,X2_58,X0_58)
% 23.66/3.49      | sP0(X1_58,X3_58,X2_58,X0_58) = iProver_top
% 23.66/3.49      | r1_tsep_1(X2_58,X3_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 23.66/3.49      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.49      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.49      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.49      | v2_struct_0(X0_58) = iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_13224,c_38769]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_27,plain,
% 23.66/3.49      ( ~ sP0(sK4(X0,X1,X2),X2,X1,X0)
% 23.66/3.49      | r3_tsep_1(X0,X1,X2)
% 23.66/3.49      | ~ r1_tsep_1(X1,X2)
% 23.66/3.49      | ~ m1_pre_topc(X2,X0)
% 23.66/3.49      | ~ m1_pre_topc(X1,X0)
% 23.66/3.49      | ~ v2_pre_topc(X0)
% 23.66/3.49      | ~ l1_pre_topc(X0)
% 23.66/3.49      | v2_struct_0(X0)
% 23.66/3.49      | v2_struct_0(X1)
% 23.66/3.49      | v2_struct_0(X2) ),
% 23.66/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_11844,plain,
% 23.66/3.49      ( ~ sP0(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
% 23.66/3.49      | r3_tsep_1(X0_58,X1_58,X2_58)
% 23.66/3.49      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.49      | ~ m1_pre_topc(X2_58,X0_58)
% 23.66/3.49      | ~ m1_pre_topc(X1_58,X0_58)
% 23.66/3.49      | ~ v2_pre_topc(X0_58)
% 23.66/3.49      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_27]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13226,plain,
% 23.66/3.50      ( sP0(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58) != iProver_top
% 23.66/3.50      | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11844]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38830,plain,
% 23.66/3.50      ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
% 23.66/3.50      | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK4(X0_58,X1_58,X2_58)) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK4(X0_58,X1_58,X2_58)) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(sK4(X0_58,X1_58,X2_58)) = iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_38772,c_13226]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_28,plain,
% 23.66/3.50      ( r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | l1_pre_topc(sK4(X0,X1,X2))
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11843,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X0_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,X0_58)
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | l1_pre_topc(sK4(X0_58,X1_58,X2_58))
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_28]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11931,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK4(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11843]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_29,plain,
% 23.66/3.50      ( r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | v2_pre_topc(sK4(X0,X1,X2))
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11842,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X0_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,X0_58)
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | v2_pre_topc(sK4(X0_58,X1_58,X2_58))
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_29]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11932,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK4(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11842]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30,plain,
% 23.66/3.50      ( r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | ~ v2_struct_0(sK4(X0,X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f87]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11841,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X0_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,X0_58)
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | ~ v2_struct_0(sK4(X0_58,X1_58,X2_58)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_30]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11933,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(sK4(X0_58,X1_58,X2_58)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11841]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38833,plain,
% 23.66/3.50      ( v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_38830,c_11931,c_11932,c_11933]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38834,plain,
% 23.66/3.50      ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
% 23.66/3.50      | r3_tsep_1(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_38833]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_41,plain,
% 23.66/3.50      ( sP2(X0,X1,X2)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) ),
% 23.66/3.50      inference(cnf_transformation,[],[f106]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11837,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | m1_subset_1(sK6(X0_58,X1_58,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))))) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_41]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13233,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_subset_1(sK6(X0_58,X1_58,X2_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11837]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_51,plain,
% 23.66/3.50      ( sP1(X0,X1,X2,X3,X4)
% 23.66/3.50      | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 23.66/3.50      inference(cnf_transformation,[],[f115]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11827,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.50      | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_51]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13243,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11827]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_10,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 23.66/3.50      | ~ m1_pre_topc(X1,X5)
% 23.66/3.50      | ~ m1_pre_topc(X4,X5)
% 23.66/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 23.66/3.50      | ~ v2_pre_topc(X2)
% 23.66/3.50      | ~ v2_pre_topc(X5)
% 23.66/3.50      | ~ l1_pre_topc(X2)
% 23.66/3.50      | ~ l1_pre_topc(X5)
% 23.66/3.50      | v2_struct_0(X5)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | ~ v1_funct_1(X0)
% 23.66/3.50      | ~ v1_funct_1(X3)
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11857,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X3_58)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,X3_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X3_58)
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(X3_58)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(X3_58)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_10]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13213,plain,
% 23.66/3.50      ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X0_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11857]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_17139,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X5_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X4_58,X5_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X5_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X5_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X4_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X5_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_13243,c_13213]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_53,plain,
% 23.66/3.50      ( sP1(X0,X1,X2,X3,X4)
% 23.66/3.50      | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f113]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11825,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.50      | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_53]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11957,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11825]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_54,plain,
% 23.66/3.50      ( sP1(X0,X1,X2,X3,X4) | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f112]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11824,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.50      | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_54]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11960,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11824]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_18104,plain,
% 23.66/3.50      ( v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top
% 23.66/3.50      | v2_struct_0(X5_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X4_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | l1_pre_topc(X5_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X5_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | m1_pre_topc(X4_58,X5_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X5_58) != iProver_top
% 23.66/3.50      | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_17139,c_11957,c_11960]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_18105,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X4_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X5_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X4_58,X5_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X5_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X5_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X4_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X5_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X5_58,X0_58,X4_58,X1_58,X1_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) = iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_18104]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37,plain,
% 23.66/3.50      ( r4_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f97]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_34,plain,
% 23.66/3.50      ( ~ r4_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ v5_pre_topc(X3,X2,X4)
% 23.66/3.50      | ~ v5_pre_topc(X5,X1,X4)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 23.66/3.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 23.66/3.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 23.66/3.50      | ~ v2_pre_topc(X4)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X4)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | ~ v1_funct_1(X3)
% 23.66/3.50      | ~ v1_funct_1(X5) ),
% 23.66/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1048,plain,
% 23.66/3.50      ( ~ r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ v5_pre_topc(X3,X2,X4)
% 23.66/3.50      | ~ v5_pre_topc(X5,X1,X4)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 23.66/3.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 23.66/3.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ v2_pre_topc(X4)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X4)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | ~ v1_funct_1(X3)
% 23.66/3.50      | ~ v1_funct_1(X5) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_37,c_34]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38,plain,
% 23.66/3.50      ( ~ r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1052,plain,
% 23.66/3.50      ( ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 23.66/3.50      | ~ v5_pre_topc(X5,X1,X4)
% 23.66/3.50      | ~ v5_pre_topc(X3,X2,X4)
% 23.66/3.50      | ~ r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 23.66/3.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ v2_pre_topc(X4)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X4)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | ~ v1_funct_1(X3)
% 23.66/3.50      | ~ v1_funct_1(X5) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_1048,c_38,c_37,c_34]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1053,plain,
% 23.66/3.50      ( ~ r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | ~ v5_pre_topc(X3,X2,X4)
% 23.66/3.50      | ~ v5_pre_topc(X5,X1,X4)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 23.66/3.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 23.66/3.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ v2_pre_topc(X4)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X4)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | ~ v1_funct_1(X3)
% 23.66/3.50      | ~ v1_funct_1(X5) ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_1052]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11807,plain,
% 23.66/3.50      ( ~ r3_tsep_1(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ v5_pre_topc(X0_59,X2_58,X3_58)
% 23.66/3.50      | ~ v5_pre_topc(X1_59,X1_58,X3_58)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X0_58,X3_58,X1_58,X2_58,X1_59,X0_59),k1_tsep_1(X0_58,X1_58,X2_58),X3_58)
% 23.66/3.50      | ~ v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X3_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X3_58))
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X0_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,X0_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X3_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58))))
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ v2_pre_topc(X3_58)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(X3_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(X3_58)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(X1_59) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_1053]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13263,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(X0_59,X2_58,X3_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(X1_59,X1_58,X3_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X0_58,X3_58,X1_58,X2_58,X1_59,X0_59),k1_tsep_1(X0_58,X1_58,X2_58),X3_58) = iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X3_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X3_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X3_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11807]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_9,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 23.66/3.50      | ~ m1_pre_topc(X1,X5)
% 23.66/3.50      | ~ m1_pre_topc(X4,X5)
% 23.66/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 23.66/3.50      | ~ v2_pre_topc(X2)
% 23.66/3.50      | ~ v2_pre_topc(X5)
% 23.66/3.50      | ~ l1_pre_topc(X2)
% 23.66/3.50      | ~ l1_pre_topc(X5)
% 23.66/3.50      | v2_struct_0(X5)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | ~ v1_funct_1(X0)
% 23.66/3.50      | ~ v1_funct_1(X3) ),
% 23.66/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11858,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X3_58)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,X3_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X3_58)
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(X3_58)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(X3_58)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(X1_59) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_9]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13212,plain,
% 23.66/3.50      ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58)) = iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X0_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11858]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_8,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.66/3.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 23.66/3.50      | ~ m1_pre_topc(X1,X5)
% 23.66/3.50      | ~ m1_pre_topc(X4,X5)
% 23.66/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.66/3.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 23.66/3.50      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 23.66/3.50      | ~ v2_pre_topc(X2)
% 23.66/3.50      | ~ v2_pre_topc(X5)
% 23.66/3.50      | ~ l1_pre_topc(X2)
% 23.66/3.50      | ~ l1_pre_topc(X5)
% 23.66/3.50      | v2_struct_0(X5)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X4)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | ~ v1_funct_1(X0)
% 23.66/3.50      | ~ v1_funct_1(X3) ),
% 23.66/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11859,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X3_58)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,X3_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 23.66/3.50      | m1_subset_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X3_58)
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(X3_58)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(X3_58)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(X1_59) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_8]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13211,plain,
% 23.66/3.50      ( v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X2_58),u1_struct_0(X1_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X0_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(k10_tmap_1(X3_58,X1_58,X2_58,X0_58,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X0_58)),u1_struct_0(X1_58)))) = iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X1_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X1_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11859]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_50,plain,
% 23.66/3.50      ( sP1(X0,X1,X2,X3,X4)
% 23.66/3.50      | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
% 23.66/3.50      | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 23.66/3.50      | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 23.66/3.50      | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ),
% 23.66/3.50      inference(cnf_transformation,[],[f116]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11828,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.50      | ~ v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
% 23.66/3.50      | ~ v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))
% 23.66/3.50      | ~ m1_subset_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_50]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13242,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_subset_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11828]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_17609,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_13211,c_13242]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11951,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11827]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_21976,plain,
% 23.66/3.50      ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_17609,c_11951,c_11957,c_11960]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_21977,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),u1_struct_0(k1_tsep_1(X3_58,X2_58,X1_58)),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_21976]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_21983,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_13212,c_21977]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_23291,plain,
% 23.66/3.50      ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_21983,c_11951,c_11957,c_11960]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_23292,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59)),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_23291]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_23297,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK7(X0_58,X1_58,X2_58,X3_58,X0_59)) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_13263,c_23292]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_52,plain,
% 23.66/3.50      ( sP1(X0,X1,X2,X3,X4) | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ),
% 23.66/3.50      inference(cnf_transformation,[],[f114]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11826,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.50      | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_52]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11954,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | v5_pre_topc(sK7(X0_58,X1_58,X2_58,X3_58,X0_59),X1_58,X0_58) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11826]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27542,plain,
% 23.66/3.50      ( v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_23297,c_11951,c_11954,c_11957,c_11960]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27543,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,sK7(X0_58,X1_58,X2_58,X3_58,X0_59))) != iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_27542]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27548,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) = iProver_top
% 23.66/3.50      | r3_tsep_1(X3_58,X2_58,X1_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(X0_59,X2_58,X0_58) != iProver_top
% 23.66/3.50      | v1_funct_2(X0_59,u1_struct_0(X2_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 23.66/3.50      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X3_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v1_funct_1(X0_59) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_18105,c_27543]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27556,plain,
% 23.66/3.50      ( sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r3_tsep_1(X4_58,X1_58,X3_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58)) != iProver_top
% 23.66/3.50      | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))) != iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X3_58,X4_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X4_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X4_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) != iProver_top
% 23.66/3.50      | l1_pre_topc(X4_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) != iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X4_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top
% 23.66/3.50      | v2_struct_0(sK5(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | v1_funct_1(sK6(X0_58,X1_58,X2_58)) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_13233,c_27548]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_42,plain,
% 23.66/3.50      ( sP2(X0,X1,X2)
% 23.66/3.50      | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
% 23.66/3.50      | ~ r1_tsep_1(X1,X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f105]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11836,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58))
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_42]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11938,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | v5_pre_topc(sK6(X0_58,X1_58,X2_58),X1_58,sK5(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11836]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_43,plain,
% 23.66/3.50      ( sP2(X0,X1,X2)
% 23.66/3.50      | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
% 23.66/3.50      | ~ r1_tsep_1(X1,X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f104]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11835,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58)))
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_43]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11939,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | v1_funct_2(sK6(X0_58,X1_58,X2_58),u1_struct_0(X1_58),u1_struct_0(sK5(X0_58,X1_58,X2_58))) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11835]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_44,plain,
% 23.66/3.50      ( sP2(X0,X1,X2) | ~ r1_tsep_1(X1,X2) | v1_funct_1(sK6(X0,X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11834,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | v1_funct_1(sK6(X0_58,X1_58,X2_58)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_44]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11940,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | v1_funct_1(sK6(X0_58,X1_58,X2_58)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11834]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_45,plain,
% 23.66/3.50      ( sP2(X0,X1,X2) | ~ r1_tsep_1(X1,X2) | l1_pre_topc(sK5(X0,X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f102]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11833,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_45]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11941,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11833]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_46,plain,
% 23.66/3.50      ( sP2(X0,X1,X2) | ~ r1_tsep_1(X1,X2) | v2_pre_topc(sK5(X0,X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f101]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11832,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_46]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11942,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(X0_58,X1_58,X2_58)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11832]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_47,plain,
% 23.66/3.50      ( sP2(X0,X1,X2)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ v2_struct_0(sK5(X0,X1,X2)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11831,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | ~ v2_struct_0(sK5(X0_58,X1_58,X2_58)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_47]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11943,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | v2_struct_0(sK5(X0_58,X1_58,X2_58)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11831]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27682,plain,
% 23.66/3.50      ( l1_pre_topc(X4_58) != iProver_top
% 23.66/3.50      | sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r3_tsep_1(X4_58,X1_58,X3_58) != iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X3_58,X4_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X4_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X4_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X4_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_27556,c_11938,c_11939,c_11940,c_11941,c_11942,c_11943]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27683,plain,
% 23.66/3.50      ( sP1(sK5(X0_58,X1_58,X2_58),X3_58,X1_58,X4_58,sK6(X0_58,X1_58,X2_58)) = iProver_top
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r3_tsep_1(X4_58,X1_58,X3_58) != iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X3_58,X4_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X4_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X4_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X4_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X4_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X3_58) = iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_27682]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_40,plain,
% 23.66/3.50      ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
% 23.66/3.50      | sP2(X0,X1,X2)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f107]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11838,plain,
% 23.66/3.50      ( ~ sP1(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58,sK6(X0_58,X1_58,X2_58))
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58)
% 23.66/3.50      | ~ r1_tsep_1(X1_58,X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_40]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13232,plain,
% 23.66/3.50      ( sP1(sK5(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58,sK6(X0_58,X1_58,X2_58)) != iProver_top
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11838]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27688,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_27683,c_13232]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11839,plain,
% 23.66/3.50      ( ~ r3_tsep_1(X0_58,X1_58,X2_58)
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(X2_58,X0_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,X0_58)
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_38]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11935,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) = iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11839]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27694,plain,
% 23.66/3.50      ( r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_27688,c_11935]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_27695,plain,
% 23.66/3.50      ( sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r3_tsep_1(X0_58,X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_27694]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38837,plain,
% 23.66/3.50      ( k10_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),X1_58,X2_58,k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X1_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)),k3_tmap_1(X0_58,sK4(X0_58,X1_58,X2_58),k1_tsep_1(X0_58,X1_58,X2_58),X2_58,sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58))) = sK3(sK4(X0_58,X1_58,X2_58),X2_58,X1_58,X0_58)
% 23.66/3.50      | sP2(X0_58,X1_58,X2_58) = iProver_top
% 23.66/3.50      | r1_tsep_1(X1_58,X2_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 23.66/3.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 23.66/3.50      | v2_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | l1_pre_topc(X0_58) != iProver_top
% 23.66/3.50      | v2_struct_0(X0_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X1_58) = iProver_top
% 23.66/3.50      | v2_struct_0(X2_58) = iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_38834,c_27695]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_59,negated_conjecture,
% 23.66/3.50      ( ~ sP2(sK8,sK9,sK10) | ~ r3_tsep_1(sK8,sK9,sK10) ),
% 23.66/3.50      inference(cnf_transformation,[],[f125]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11819,negated_conjecture,
% 23.66/3.50      ( ~ sP2(sK8,sK9,sK10) | ~ r3_tsep_1(sK8,sK9,sK10) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_59]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13251,plain,
% 23.66/3.50      ( sP2(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11819]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38906,plain,
% 23.66/3.50      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_38837,c_13251]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_67,negated_conjecture,
% 23.66/3.50      ( ~ v2_struct_0(sK8) ),
% 23.66/3.50      inference(cnf_transformation,[],[f117]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_68,plain,
% 23.66/3.50      ( v2_struct_0(sK8) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_66,negated_conjecture,
% 23.66/3.50      ( v2_pre_topc(sK8) ),
% 23.66/3.50      inference(cnf_transformation,[],[f118]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_69,plain,
% 23.66/3.50      ( v2_pre_topc(sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_65,negated_conjecture,
% 23.66/3.50      ( l1_pre_topc(sK8) ),
% 23.66/3.50      inference(cnf_transformation,[],[f119]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_70,plain,
% 23.66/3.50      ( l1_pre_topc(sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_64,negated_conjecture,
% 23.66/3.50      ( ~ v2_struct_0(sK9) ),
% 23.66/3.50      inference(cnf_transformation,[],[f120]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_71,plain,
% 23.66/3.50      ( v2_struct_0(sK9) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_63,negated_conjecture,
% 23.66/3.50      ( m1_pre_topc(sK9,sK8) ),
% 23.66/3.50      inference(cnf_transformation,[],[f121]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_72,plain,
% 23.66/3.50      ( m1_pre_topc(sK9,sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_62,negated_conjecture,
% 23.66/3.50      ( ~ v2_struct_0(sK10) ),
% 23.66/3.50      inference(cnf_transformation,[],[f122]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_73,plain,
% 23.66/3.50      ( v2_struct_0(sK10) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_61,negated_conjecture,
% 23.66/3.50      ( m1_pre_topc(sK10,sK8) ),
% 23.66/3.50      inference(cnf_transformation,[],[f123]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_74,plain,
% 23.66/3.50      ( m1_pre_topc(sK10,sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_524,plain,
% 23.66/3.50      ( ~ sP2(sK8,sK9,sK10) | ~ r3_tsep_1(sK8,sK9,sK10) ),
% 23.66/3.50      inference(prop_impl,[status(thm)],[c_59]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1491,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0,X1)
% 23.66/3.50      | ~ v2_struct_0(sK5(X2,X0,X1))
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_47,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1492,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | ~ v2_struct_0(sK5(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1491]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1493,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1504,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0,X1)
% 23.66/3.50      | v2_pre_topc(sK5(X2,X0,X1))
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_46,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1505,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | v2_pre_topc(sK5(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1504]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1506,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(sK8,sK9,sK10)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1517,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0,X1)
% 23.66/3.50      | l1_pre_topc(sK5(X2,X0,X1))
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_45,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1518,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | l1_pre_topc(sK5(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1517]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1519,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(sK8,sK9,sK10)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1530,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0,X1)
% 23.66/3.50      | v1_funct_1(sK6(X2,X0,X1))
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_44,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1531,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | v1_funct_1(sK6(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1530]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1532,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | v1_funct_1(sK6(sK8,sK9,sK10)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1543,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | sK10 != X2
% 23.66/3.50      | sK9 != X1
% 23.66/3.50      | sK8 != X0 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_43,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1544,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1543]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1545,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) = iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1556,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | sK10 != X2
% 23.66/3.50      | sK9 != X1
% 23.66/3.50      | sK8 != X0 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_42,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1557,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1556]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1558,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1569,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0,X1)
% 23.66/3.50      | m1_subset_1(sK6(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5(X2,X0,X1)))))
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_41,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1570,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1569]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1571,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1582,plain,
% 23.66/3.50      ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
% 23.66/3.50      | ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X1,X2)
% 23.66/3.50      | sK10 != X2
% 23.66/3.50      | sK9 != X1
% 23.66/3.50      | sK8 != X0 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_40,c_524]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1583,plain,
% 23.66/3.50      ( ~ sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
% 23.66/3.50      | ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1582]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1584,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_32,plain,
% 23.66/3.50      ( ~ r3_tsep_1(X0,X1,X2)
% 23.66/3.50      | r1_tsep_1(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X2,X0)
% 23.66/3.50      | ~ m1_pre_topc(X1,X0)
% 23.66/3.50      | ~ v2_pre_topc(X0)
% 23.66/3.50      | ~ l1_pre_topc(X0)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | v2_struct_0(X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_60,negated_conjecture,
% 23.66/3.50      ( sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10) ),
% 23.66/3.50      inference(cnf_transformation,[],[f124]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_526,plain,
% 23.66/3.50      ( sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10) ),
% 23.66/3.50      inference(prop_impl,[status(thm)],[c_60]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_6260,plain,
% 23.66/3.50      ( sP2(sK8,sK9,sK10)
% 23.66/3.50      | r1_tsep_1(X0,X1)
% 23.66/3.50      | ~ m1_pre_topc(X1,X2)
% 23.66/3.50      | ~ m1_pre_topc(X0,X2)
% 23.66/3.50      | ~ v2_pre_topc(X2)
% 23.66/3.50      | ~ l1_pre_topc(X2)
% 23.66/3.50      | v2_struct_0(X2)
% 23.66/3.50      | v2_struct_0(X0)
% 23.66/3.50      | v2_struct_0(X1)
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_32,c_526]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_6261,plain,
% 23.66/3.50      ( sP2(sK8,sK9,sK10)
% 23.66/3.50      | r1_tsep_1(sK9,sK10)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_6260]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_49,plain,
% 23.66/3.50      ( ~ sP2(X0,X1,X2) | r1_tsep_1(X1,X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f98]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1595,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | r1_tsep_1(X0,X1)
% 23.66/3.50      | sK10 != X1
% 23.66/3.50      | sK9 != X0
% 23.66/3.50      | sK8 != X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_49,c_526]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1596,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) | r1_tsep_1(sK9,sK10) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_1595]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_6263,plain,
% 23.66/3.50      ( r1_tsep_1(sK9,sK10) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_6261,c_67,c_66,c_65,c_64,c_63,c_62,c_61,c_59,c_1596]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_6265,plain,
% 23.66/3.50      ( r1_tsep_1(sK9,sK10) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_6263]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14808,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
% 23.66/3.50      | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11824]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14809,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14808]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14807,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
% 23.66/3.50      | v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11826]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14811,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14807]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14806,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
% 23.66/3.50      | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11825]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14813,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14806]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14805,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
% 23.66/3.50      | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11827]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14815,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14805]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14803,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))
% 23.66/3.50      | ~ v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11828]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14819,plain,
% 23.66/3.50      ( sP1(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14803]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13507,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X0_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(sK10,X2_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ v2_pre_topc(X2_58)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(X2_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | v1_funct_1(k10_tmap_1(X2_58,X1_58,X0_58,sK10,X0_59,X1_59)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11857]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_24300,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | v1_funct_1(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13507]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_26411,plain,
% 23.66/3.50      ( ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))))
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_24300]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_26412,plain,
% 23.66/3.50      ( v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top
% 23.66/3.50      | v1_funct_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_26411]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13506,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
% 23.66/3.50      | v1_funct_2(k10_tmap_1(X2_58,X1_58,X0_58,sK10,X0_59,X1_59),u1_struct_0(k1_tsep_1(X2_58,X0_58,sK10)),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X0_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(sK10,X2_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ v2_pre_topc(X2_58)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(X2_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11858]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_24340,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
% 23.66/3.50      | v1_funct_2(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(X0_58))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13506]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_28149,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,X0_59,sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_24340]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30136,plain,
% 23.66/3.50      ( v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_28149]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30137,plain,
% 23.66/3.50      ( v1_funct_2(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))) = iProver_top
% 23.66/3.50      | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_30136]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_36825,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X0_58,X2_58)
% 23.66/3.50      | ~ m1_pre_topc(sK10,X2_58)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
% 23.66/3.50      | m1_subset_1(k10_tmap_1(X2_58,X1_58,X0_58,sK10,X0_59,X1_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_58,X0_58,sK10)),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ v2_pre_topc(X2_58)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(X2_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11859]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37069,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
% 23.66/3.50      | m1_subset_1(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_36825]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37715,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,X0_59,sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_37069]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37925,plain,
% 23.66/3.50      ( ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_37715]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37926,plain,
% 23.66/3.50      ( v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | m1_subset_1(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK8,sK9,sK10)),u1_struct_0(sK5(sK8,sK9,sK10))))) = iProver_top
% 23.66/3.50      | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_37925]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_36661,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,X0_58,X1_58)
% 23.66/3.50      | ~ v5_pre_topc(X0_59,X1_58,X2_58)
% 23.66/3.50      | ~ v5_pre_topc(X1_59,X0_58,X2_58)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,X2_58,X0_58,X1_58,X1_59,X0_59),k1_tsep_1(sK8,X0_58,X1_58),X2_58)
% 23.66/3.50      | ~ v1_funct_2(X0_59,u1_struct_0(X1_58),u1_struct_0(X2_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(X0_58),u1_struct_0(X2_58))
% 23.66/3.50      | ~ m1_pre_topc(X1_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X2_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X2_58))))
% 23.66/3.50      | ~ v2_pre_topc(X2_58)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(X2_58)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(X2_58)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(X1_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11807]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37096,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,X0_58,sK10)
% 23.66/3.50      | ~ v5_pre_topc(X0_59,X0_58,X1_58)
% 23.66/3.50      | ~ v5_pre_topc(X1_59,sK10,X1_58)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,X1_58,X0_58,sK10,X0_59,X1_59),k1_tsep_1(sK8,X0_58,sK10),X1_58)
% 23.66/3.50      | ~ v1_funct_2(X0_59,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK10),u1_struct_0(X1_58))
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1_58))))
% 23.66/3.50      | ~ v2_pre_topc(X1_58)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(X1_58)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_36661]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37529,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ v5_pre_topc(X0_59,sK10,X0_58)
% 23.66/3.50      | ~ v5_pre_topc(X1_59,sK9,X0_58)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,X0_58,sK9,sK10,X1_59,X0_59),k1_tsep_1(sK8,sK9,sK10),X0_58)
% 23.66/3.50      | ~ v1_funct_2(X0_59,u1_struct_0(sK10),u1_struct_0(X0_58))
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(sK9),u1_struct_0(X0_58))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ v2_pre_topc(X0_58)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(X0_58)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X1_59)
% 23.66/3.50      | ~ v1_funct_1(X0_59) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_37096]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37888,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ v5_pre_topc(X0_59,sK9,sK5(sK8,sK9,sK10))
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,X0_59,sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v1_funct_2(X0_59,u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(X0_59)
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_37529]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38267,plain,
% 23.66/3.50      ( ~ r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10)))))
% 23.66/3.50      | ~ v2_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK5(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8)
% 23.66/3.50      | ~ v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)))
% 23.66/3.50      | ~ v1_funct_1(sK6(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_37888]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38268,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(sK8,sK5(sK8,sK9,sK10),sK9,sK10,sK6(sK8,sK9,sK10),sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))),k1_tsep_1(sK8,sK9,sK10),sK5(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v5_pre_topc(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),sK10,sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v5_pre_topc(sK6(sK8,sK9,sK10),sK9,sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v1_funct_2(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_2(sK6(sK8,sK9,sK10),u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | m1_subset_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | m1_subset_1(sK6(sK8,sK9,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK5(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK5(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK5(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top
% 23.66/3.50      | v1_funct_1(sK7(sK5(sK8,sK9,sK10),sK10,sK9,sK8,sK6(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | v1_funct_1(sK6(sK8,sK9,sK10)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_38267]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38910,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_38906,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_1493,
% 23.66/3.50                 c_1506,c_1519,c_1532,c_1545,c_1558,c_1571,c_1584,c_6265,
% 23.66/3.50                 c_14809,c_14811,c_14813,c_14815,c_14819,c_26412,c_30137,
% 23.66/3.50                 c_37926,c_38268]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_38914,plain,
% 23.66/3.50      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_38834,c_38910]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39035,plain,
% 23.66/3.50      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_38914,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_6265]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_56,plain,
% 23.66/3.50      ( ~ sP1(X0,X1,X2,X3,X4)
% 23.66/3.50      | ~ v5_pre_topc(X5,X1,X0)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
% 23.66/3.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
% 23.66/3.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 23.66/3.50      | ~ v1_funct_1(X5) ),
% 23.66/3.50      inference(cnf_transformation,[],[f110]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11822,plain,
% 23.66/3.50      ( ~ sP1(X0_58,X1_58,X2_58,X3_58,X0_59)
% 23.66/3.50      | ~ v5_pre_topc(X1_59,X1_58,X0_58)
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,X1_59),k1_tsep_1(X3_58,X2_58,X1_58),X0_58)
% 23.66/3.50      | ~ v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X0_58))
% 23.66/3.50      | ~ m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58))))
% 23.66/3.50      | ~ v1_funct_1(X1_59) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_56]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13248,plain,
% 23.66/3.50      ( sP1(X0_58,X1_58,X2_58,X3_58,X0_59) != iProver_top
% 23.66/3.50      | v5_pre_topc(X1_59,X1_58,X0_58) != iProver_top
% 23.66/3.50      | v5_pre_topc(k10_tmap_1(X3_58,X0_58,X2_58,X1_58,X0_59,X1_59),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) = iProver_top
% 23.66/3.50      | v1_funct_2(X1_59,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 23.66/3.50      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 23.66/3.50      | v1_funct_1(X1_59) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_11822]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39045,plain,
% 23.66/3.50      ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
% 23.66/3.50      | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
% 23.66/3.50      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_39035,c_13248]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13346,plain,
% 23.66/3.50      ( ~ sP0(sK4(sK8,X0_58,X1_58),X1_58,X0_58,sK8)
% 23.66/3.50      | r3_tsep_1(sK8,X0_58,X1_58)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,X1_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11844]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13665,plain,
% 23.66/3.50      ( ~ sP0(sK4(sK8,X0_58,sK10),sK10,X0_58,sK8)
% 23.66/3.50      | r3_tsep_1(sK8,X0_58,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,sK10)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13346]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13870,plain,
% 23.66/3.50      ( ~ sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13665]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13871,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) != iProver_top
% 23.66/3.50      | r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_13870]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11,plain,
% 23.66/3.50      ( sP0(X0,X1,X2,X3)
% 23.66/3.50      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
% 23.66/3.50      | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 23.66/3.50      | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 23.66/3.50      | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_424,plain,
% 23.66/3.50      ( ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
% 23.66/3.50      | sP0(X0,X1,X2,X3) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_11,c_22,c_21,c_20]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_425,plain,
% 23.66/3.50      ( sP0(X0,X1,X2,X3)
% 23.66/3.50      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_424]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11810,plain,
% 23.66/3.50      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.50      | ~ v5_pre_topc(sK3(X0_58,X1_58,X2_58,X3_58),k1_tsep_1(X3_58,X2_58,X1_58),X0_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_425]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14155,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | ~ v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11810]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14159,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14155]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14153,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11853]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14163,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14153]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13,plain,
% 23.66/3.50      ( sP0(X0,X1,X2,X3)
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ),
% 23.66/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11855,plain,
% 23.66/3.50      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X1_58,sK3(X0_58,X1_58,X2_58,X3_58)),X1_58,X0_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_13]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14150,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11855]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14169,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14150]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14148,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11854]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14173,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14148]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14146,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11856]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14177,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14146]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39136,plain,
% 23.66/3.50      ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_39045,c_68,c_69,c_70,c_71,c_72,c_73,c_74,c_1493,
% 23.66/3.50                 c_1506,c_1519,c_1532,c_1545,c_1558,c_1571,c_1584,c_6265,
% 23.66/3.50                 c_13871,c_14159,c_14163,c_14169,c_14173,c_14177,c_14809,
% 23.66/3.50                 c_14811,c_14813,c_14815,c_14819,c_26412,c_30137,c_37926,
% 23.66/3.50                 c_38268]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39141,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | sP2(sK8,sK9,sK10) != iProver_top
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_17765,c_39136]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_17,plain,
% 23.66/3.50      ( sP0(X0,X1,X2,X3)
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ),
% 23.66/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11851,plain,
% 23.66/3.50      ( sP0(X0_58,X1_58,X2_58,X3_58)
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(X3_58,X0_58,k1_tsep_1(X3_58,X2_58,X1_58),X2_58,sK3(X0_58,X1_58,X2_58,X3_58)),X2_58,X0_58) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_17]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14149,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11851]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14171,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK9,sK4(sK8,sK9,sK10)) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14149]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14152,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 23.66/3.50      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11849]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14165,plain,
% 23.66/3.50      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 23.66/3.50      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_14152]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13349,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,X0_58,X1_58)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,X1_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | l1_pre_topc(sK4(sK8,X0_58,X1_58))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11843]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13653,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,X0_58,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,sK10)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | l1_pre_topc(sK4(sK8,X0_58,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13349]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13867,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | l1_pre_topc(sK4(sK8,sK9,sK10))
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13653]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13868,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK4(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_13867]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13348,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,X0_58,X1_58)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,X1_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | v2_pre_topc(sK4(sK8,X0_58,X1_58))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11842]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13643,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,X0_58,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,sK10)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | v2_pre_topc(sK4(sK8,X0_58,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13348]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13858,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | v2_pre_topc(sK4(sK8,sK9,sK10))
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13643]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13859,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK4(sK8,sK9,sK10)) = iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_13858]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13347,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,X0_58,X1_58)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,X1_58)
% 23.66/3.50      | ~ m1_pre_topc(X1_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | v2_struct_0(X1_58)
% 23.66/3.50      | ~ v2_struct_0(sK4(sK8,X0_58,X1_58))
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_11841]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13633,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,X0_58,sK10)
% 23.66/3.50      | ~ r1_tsep_1(X0_58,sK10)
% 23.66/3.50      | ~ m1_pre_topc(X0_58,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | v2_struct_0(X0_58)
% 23.66/3.50      | ~ v2_struct_0(sK4(sK8,X0_58,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13347]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13855,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10)
% 23.66/3.50      | ~ r1_tsep_1(sK9,sK10)
% 23.66/3.50      | ~ m1_pre_topc(sK10,sK8)
% 23.66/3.50      | ~ m1_pre_topc(sK9,sK8)
% 23.66/3.50      | ~ v2_pre_topc(sK8)
% 23.66/3.50      | ~ l1_pre_topc(sK8)
% 23.66/3.50      | ~ v2_struct_0(sK4(sK8,sK9,sK10))
% 23.66/3.50      | v2_struct_0(sK10)
% 23.66/3.50      | v2_struct_0(sK9)
% 23.66/3.50      | v2_struct_0(sK8) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_13633]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13856,plain,
% 23.66/3.50      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 23.66/3.50      | r1_tsep_1(sK9,sK10) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 23.66/3.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 23.66/3.50      | v2_pre_topc(sK8) != iProver_top
% 23.66/3.50      | l1_pre_topc(sK8) != iProver_top
% 23.66/3.50      | v2_struct_0(sK4(sK8,sK9,sK10)) != iProver_top
% 23.66/3.50      | v2_struct_0(sK10) = iProver_top
% 23.66/3.50      | v2_struct_0(sK9) = iProver_top
% 23.66/3.50      | v2_struct_0(sK8) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_13855]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_75,plain,
% 23.66/3.50      ( sP2(sK8,sK9,sK10) = iProver_top
% 23.66/3.50      | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(contradiction,plain,
% 23.66/3.50      ( $false ),
% 23.66/3.50      inference(minisat,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_39141,c_38910,c_14171,c_14165,c_13871,c_13868,c_13859,
% 23.66/3.50                 c_13856,c_6265,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68]) ).
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  ------                               Statistics
% 23.66/3.50  
% 23.66/3.50  ------ General
% 23.66/3.50  
% 23.66/3.50  abstr_ref_over_cycles:                  0
% 23.66/3.50  abstr_ref_under_cycles:                 0
% 23.66/3.50  gc_basic_clause_elim:                   0
% 23.66/3.50  forced_gc_time:                         0
% 23.66/3.50  parsing_time:                           0.017
% 23.66/3.50  unif_index_cands_time:                  0.
% 23.66/3.50  unif_index_add_time:                    0.
% 23.66/3.50  orderings_time:                         0.
% 23.66/3.50  out_proof_time:                         0.042
% 23.66/3.50  total_time:                             2.648
% 23.66/3.50  num_of_symbols:                         63
% 23.66/3.50  num_of_terms:                           58301
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing
% 23.66/3.50  
% 23.66/3.50  num_of_splits:                          0
% 23.66/3.50  num_of_split_atoms:                     0
% 23.66/3.50  num_of_reused_defs:                     0
% 23.66/3.50  num_eq_ax_congr_red:                    146
% 23.66/3.50  num_of_sem_filtered_clauses:            1
% 23.66/3.50  num_of_subtypes:                        5
% 23.66/3.50  monotx_restored_types:                  0
% 23.66/3.50  sat_num_of_epr_types:                   0
% 23.66/3.50  sat_num_of_non_cyclic_types:            0
% 23.66/3.50  sat_guarded_non_collapsed_types:        1
% 23.66/3.50  num_pure_diseq_elim:                    0
% 23.66/3.50  simp_replaced_by:                       0
% 23.66/3.50  res_preprocessed:                       271
% 23.66/3.50  prep_upred:                             0
% 23.66/3.50  prep_unflattend:                        380
% 23.66/3.50  smt_new_axioms:                         0
% 23.66/3.50  pred_elim_cands:                        14
% 23.66/3.50  pred_elim:                              1
% 23.66/3.50  pred_elim_cl:                           2
% 23.66/3.50  pred_elim_cycles:                       11
% 23.66/3.50  merged_defs:                            8
% 23.66/3.50  merged_defs_ncl:                        0
% 23.66/3.50  bin_hyper_res:                          8
% 23.66/3.50  prep_cycles:                            4
% 23.66/3.50  pred_elim_time:                         0.166
% 23.66/3.50  splitting_time:                         0.
% 23.66/3.50  sem_filter_time:                        0.
% 23.66/3.50  monotx_time:                            0.
% 23.66/3.50  subtype_inf_time:                       0.002
% 23.66/3.50  
% 23.66/3.50  ------ Problem properties
% 23.66/3.50  
% 23.66/3.50  clauses:                                62
% 23.66/3.50  conjectures:                            9
% 23.66/3.50  epr:                                    12
% 23.66/3.50  horn:                                   20
% 23.66/3.50  ground:                                 9
% 23.66/3.50  unary:                                  7
% 23.66/3.50  binary:                                 19
% 23.66/3.50  lits:                                   454
% 23.66/3.50  lits_eq:                                3
% 23.66/3.50  fd_pure:                                0
% 23.66/3.50  fd_pseudo:                              0
% 23.66/3.50  fd_cond:                                0
% 23.66/3.50  fd_pseudo_cond:                         3
% 23.66/3.50  ac_symbols:                             0
% 23.66/3.50  
% 23.66/3.50  ------ Propositional Solver
% 23.66/3.50  
% 23.66/3.50  prop_solver_calls:                      41
% 23.66/3.50  prop_fast_solver_calls:                 18890
% 23.66/3.50  smt_solver_calls:                       0
% 23.66/3.50  smt_fast_solver_calls:                  0
% 23.66/3.50  prop_num_of_clauses:                    15364
% 23.66/3.50  prop_preprocess_simplified:             34251
% 23.66/3.50  prop_fo_subsumed:                       978
% 23.66/3.50  prop_solver_time:                       0.
% 23.66/3.50  smt_solver_time:                        0.
% 23.66/3.50  smt_fast_solver_time:                   0.
% 23.66/3.50  prop_fast_solver_time:                  0.
% 23.66/3.50  prop_unsat_core_time:                   0.002
% 23.66/3.50  
% 23.66/3.50  ------ QBF
% 23.66/3.50  
% 23.66/3.50  qbf_q_res:                              0
% 23.66/3.50  qbf_num_tautologies:                    0
% 23.66/3.50  qbf_prep_cycles:                        0
% 23.66/3.50  
% 23.66/3.50  ------ BMC1
% 23.66/3.50  
% 23.66/3.50  bmc1_current_bound:                     -1
% 23.66/3.50  bmc1_last_solved_bound:                 -1
% 23.66/3.50  bmc1_unsat_core_size:                   -1
% 23.66/3.50  bmc1_unsat_core_parents_size:           -1
% 23.66/3.50  bmc1_merge_next_fun:                    0
% 23.66/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.66/3.50  
% 23.66/3.50  ------ Instantiation
% 23.66/3.50  
% 23.66/3.50  inst_num_of_clauses:                    398
% 23.66/3.50  inst_num_in_passive:                    0
% 23.66/3.50  inst_num_in_active:                     2804
% 23.66/3.50  inst_num_in_unprocessed:                72
% 23.66/3.50  inst_num_of_loops:                      3339
% 23.66/3.50  inst_num_of_learning_restarts:          1
% 23.66/3.50  inst_num_moves_active_passive:          524
% 23.66/3.50  inst_lit_activity:                      0
% 23.66/3.50  inst_lit_activity_moves:                1
% 23.66/3.50  inst_num_tautologies:                   0
% 23.66/3.50  inst_num_prop_implied:                  0
% 23.66/3.50  inst_num_existing_simplified:           0
% 23.66/3.50  inst_num_eq_res_simplified:             0
% 23.66/3.50  inst_num_child_elim:                    0
% 23.66/3.50  inst_num_of_dismatching_blockings:      1938
% 23.66/3.50  inst_num_of_non_proper_insts:           4110
% 23.66/3.50  inst_num_of_duplicates:                 0
% 23.66/3.50  inst_inst_num_from_inst_to_res:         0
% 23.66/3.50  inst_dismatching_checking_time:         0.
% 23.66/3.50  
% 23.66/3.50  ------ Resolution
% 23.66/3.50  
% 23.66/3.50  res_num_of_clauses:                     72
% 23.66/3.50  res_num_in_passive:                     72
% 23.66/3.50  res_num_in_active:                      0
% 23.66/3.50  res_num_of_loops:                       275
% 23.66/3.50  res_forward_subset_subsumed:            70
% 23.66/3.50  res_backward_subset_subsumed:           4
% 23.66/3.50  res_forward_subsumed:                   0
% 23.66/3.50  res_backward_subsumed:                  0
% 23.66/3.50  res_forward_subsumption_resolution:     0
% 23.66/3.50  res_backward_subsumption_resolution:    0
% 23.66/3.50  res_clause_to_clause_subsumption:       6334
% 23.66/3.50  res_orphan_elimination:                 0
% 23.66/3.50  res_tautology_del:                      213
% 23.66/3.50  res_num_eq_res_simplified:              0
% 23.66/3.50  res_num_sel_changes:                    0
% 23.66/3.50  res_moves_from_active_to_pass:          0
% 23.66/3.50  
% 23.66/3.50  ------ Superposition
% 23.66/3.50  
% 23.66/3.50  sup_time_total:                         0.
% 23.66/3.50  sup_time_generating:                    0.
% 23.66/3.50  sup_time_sim_full:                      0.
% 23.66/3.50  sup_time_sim_immed:                     0.
% 23.66/3.50  
% 23.66/3.50  sup_num_of_clauses:                     559
% 23.66/3.50  sup_num_in_active:                      379
% 23.66/3.50  sup_num_in_passive:                     180
% 23.66/3.50  sup_num_of_loops:                       667
% 23.66/3.50  sup_fw_superposition:                   853
% 23.66/3.50  sup_bw_superposition:                   257
% 23.66/3.50  sup_immediate_simplified:               216
% 23.66/3.50  sup_given_eliminated:                   93
% 23.66/3.50  comparisons_done:                       0
% 23.66/3.50  comparisons_avoided:                    0
% 23.66/3.50  
% 23.66/3.50  ------ Simplifications
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  sim_fw_subset_subsumed:                 5
% 23.66/3.50  sim_bw_subset_subsumed:                 130
% 23.66/3.50  sim_fw_subsumed:                        147
% 23.66/3.50  sim_bw_subsumed:                        278
% 23.66/3.50  sim_fw_subsumption_res:                 0
% 23.66/3.50  sim_bw_subsumption_res:                 0
% 23.66/3.50  sim_tautology_del:                      23
% 23.66/3.50  sim_eq_tautology_del:                   59
% 23.66/3.50  sim_eq_res_simp:                        0
% 23.66/3.50  sim_fw_demodulated:                     2
% 23.66/3.50  sim_bw_demodulated:                     0
% 23.66/3.50  sim_light_normalised:                   15
% 23.66/3.50  sim_joinable_taut:                      0
% 23.66/3.50  sim_joinable_simp:                      0
% 23.66/3.50  sim_ac_normalised:                      0
% 23.66/3.50  sim_smt_subsumption:                    0
% 23.66/3.50  
%------------------------------------------------------------------------------
