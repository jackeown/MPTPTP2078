%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:26 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  356 (7281 expanded)
%              Number of clauses        :  247 (2017 expanded)
%              Number of leaves         :   18 (1915 expanded)
%              Depth                    :   35
%              Number of atoms          : 2898 (100740 expanded)
%              Number of equality atoms :  983 (5606 expanded)
%              Maximal formula depth    :   28 (   9 average)
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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f51,f54,f53,f52])).

fof(f117,plain,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(rectify,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f42,f44,f43])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X6,X1,X0)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X6)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X6,X1,X0)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X6)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(sK3(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X6,X1,X0)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X6)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(definition_folding,[],[f14,f23])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f111,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f112,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f114,plain,(
    m1_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    m1_pre_topc(sK10,sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f39])).

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

fof(f86,plain,(
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

fof(f89,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v1_funct_1(sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | l1_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | v2_pre_topc(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f118,plain,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(X6,X1,X0)
      | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X6)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X4,X2,X1,X0)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11196,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_12467,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11196])).

cnf(c_55,negated_conjecture,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_11157,negated_conjecture,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(subtyping,[status(esa)],[c_55])).

cnf(c_12506,plain,
    ( sP2(sK8,sK9,sK10) = iProver_top
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11157])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11192,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_12471,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11192])).

cnf(c_43,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ sP2(X3,X2,X1)
    | ~ v5_pre_topc(X4,X2,X0)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_11169,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | ~ sP2(X3_57,X2_57,X1_57)
    | ~ v5_pre_topc(X0_58,X2_57,X0_57)
    | ~ v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57))))
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ v1_funct_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_12494,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | sP2(X3_57,X2_57,X1_57) != iProver_top
    | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11169])).

cnf(c_16032,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57))) = iProver_top
    | sP0(X0_57,X5_57,X2_57,X4_57) = iProver_top
    | sP2(X3_57,X2_57,X1_57) != iProver_top
    | v5_pre_topc(k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57)),X2_57,X0_57) != iProver_top
    | v1_funct_2(k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57)),u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12471,c_12494])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11189,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_12474,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11189])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11190,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X2_57),u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_12473,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X2_57),u1_struct_0(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11190])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11191,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),X2_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_12472,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),X2_57,X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11191])).

cnf(c_17825,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57))) = iProver_top
    | sP0(X0_57,X5_57,X2_57,X4_57) = iProver_top
    | sP2(X3_57,X2_57,X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16032,c_12474,c_12473,c_12472])).

cnf(c_52,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X5,X1,X0)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
    | v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_11160,plain,
    ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | ~ v5_pre_topc(X1_58,X1_57,X0_57)
    | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | ~ v1_funct_1(X1_58) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_12503,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11160])).

cnf(c_50,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X5,X1,X0)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_11162,plain,
    ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | ~ v5_pre_topc(X1_58,X1_57,X0_57)
    | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))))
    | ~ v1_funct_1(X1_58) ),
    inference(subtyping,[status(esa)],[c_50])).

cnf(c_12501,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) = iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11162])).

cnf(c_27,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11178,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57),X0_58,k10_tmap_1(X0_57,X3_57,X1_57,X2_57,k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X1_57,X0_58),k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X2_57,X0_58)))
    | ~ v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))))
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(X3_57)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(X3_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_58) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_12485,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57),X0_58,k10_tmap_1(X0_57,X3_57,X1_57,X2_57,k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X1_57,X0_58),k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X2_57,X0_58))) = iProver_top
    | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11178])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11188,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | m1_subset_1(sK3(X0_57,X1_57,X2_57,X3_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_12475,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | m1_subset_1(sK3(X0_57,X1_57,X2_57,X3_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11188])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11200,plain,
    ( ~ r2_funct_2(X0_59,X1_59,X0_58,X1_58)
    | ~ v1_funct_2(X1_58,X0_59,X1_59)
    | ~ v1_funct_2(X0_58,X0_59,X1_59)
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | ~ v1_funct_1(X0_58)
    | ~ v1_funct_1(X1_58)
    | X0_58 = X1_58 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_12463,plain,
    ( X0_58 = X1_58
    | r2_funct_2(X0_59,X1_59,X0_58,X1_58) != iProver_top
    | v1_funct_2(X0_58,X0_59,X1_59) != iProver_top
    | v1_funct_2(X1_58,X0_59,X1_59) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11200])).

cnf(c_14826,plain,
    ( sK3(X0_57,X1_57,X2_57,X3_57) = X0_58
    | sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | r2_funct_2(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57),sK3(X0_57,X1_57,X2_57,X3_57),X0_58) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12475,c_12463])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11187,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_11245,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11187])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(sK3(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11186,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_11246,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11186])).

cnf(c_16973,plain,
    ( v1_funct_1(X0_58) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
    | sK3(X0_57,X1_57,X2_57,X3_57) = X0_58
    | sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | r2_funct_2(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57),sK3(X0_57,X1_57,X2_57,X3_57),X0_58) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14826,c_11245,c_11246])).

cnf(c_16974,plain,
    ( sK3(X0_57,X1_57,X2_57,X3_57) = X0_58
    | sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | r2_funct_2(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57),sK3(X0_57,X1_57,X2_57,X3_57),X0_58) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_16973])).

cnf(c_16985,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(sK3(X1_57,X3_57,X2_57,X0_57),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(sK3(X1_57,X3_57,X2_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)))) != iProver_top
    | v1_funct_1(sK3(X1_57,X3_57,X2_57,X0_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12485,c_16974])).

cnf(c_12477,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11186])).

cnf(c_12476,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11187])).

cnf(c_19902,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16985,c_12477,c_12475,c_12476])).

cnf(c_19906,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),X3_57,X1_57) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),u1_struct_0(X3_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12501,c_19902])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11193,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_12470,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11193])).

cnf(c_53,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X5,X1,X0)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(X5)
    | v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_11159,plain,
    ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | ~ v5_pre_topc(X1_58,X1_57,X0_57)
    | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | ~ v1_funct_1(X1_58)
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) ),
    inference(subtyping,[status(esa)],[c_53])).

cnf(c_12504,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11159])).

cnf(c_15347,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | sP0(X0_57,X1_57,X4_57,X5_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)),X1_57,X0_57) != iProver_top
    | v1_funct_2(k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)))) = iProver_top
    | v1_funct_1(k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12467,c_12504])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_11194,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X1_57),u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_12469,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X1_57),u1_struct_0(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11194])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11195,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_12468,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),X1_57,X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11195])).

cnf(c_17555,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | sP0(X0_57,X1_57,X4_57,X5_57) = iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15347,c_12470,c_12469,c_12468])).

cnf(c_20012,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19906,c_12470,c_17555,c_12467,c_12469,c_12468])).

cnf(c_20016,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),X3_57,X1_57) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),u1_struct_0(X3_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12503,c_20012])).

cnf(c_20254,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20016,c_12470,c_12467,c_12469,c_12468])).

cnf(c_20259,plain,
    ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
    | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
    | sP2(X0_57,X2_57,X3_57) != iProver_top
    | m1_pre_topc(X3_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_17825,c_20254])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_11184,plain,
    ( ~ sP0(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
    | r3_tsep_1(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_12479,plain,
    ( sP0(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57) != iProver_top
    | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11184])).

cnf(c_20504,plain,
    ( k10_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),X1_57,X2_57,k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X1_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)),k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X2_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57))) = sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
    | sP2(X0_57,X1_57,X2_57) != iProver_top
    | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK4(X0_57,X1_57,X2_57)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK4(X0_57,X1_57,X2_57)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(sK4(X0_57,X1_57,X2_57)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20259,c_12479])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_11183,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | l1_pre_topc(sK4(X0_57,X1_57,X2_57))
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_11251,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK4(X0_57,X1_57,X2_57)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11183])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_11182,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ v2_pre_topc(X0_57)
    | v2_pre_topc(sK4(X0_57,X1_57,X2_57))
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_11252,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK4(X0_57,X1_57,X2_57)) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11182])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_11181,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | ~ v2_struct_0(sK4(X0_57,X1_57,X2_57)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_11253,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(sK4(X0_57,X1_57,X2_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11181])).

cnf(c_44,plain,
    ( ~ sP2(X0,X1,X2)
    | r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_11168,plain,
    ( ~ sP2(X0_57,X1_57,X2_57)
    | r1_tsep_1(X1_57,X2_57) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_11270,plain,
    ( sP2(X0_57,X1_57,X2_57) != iProver_top
    | r1_tsep_1(X1_57,X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11168])).

cnf(c_21008,plain,
    ( v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | k10_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),X1_57,X2_57,k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X1_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)),k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X2_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57))) = sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
    | sP2(X0_57,X1_57,X2_57) != iProver_top
    | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20504,c_11251,c_11252,c_11253,c_11270])).

cnf(c_21009,plain,
    ( k10_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),X1_57,X2_57,k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X1_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)),k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X2_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57))) = sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
    | sP2(X0_57,X1_57,X2_57) != iProver_top
    | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_21008])).

cnf(c_21022,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_12506,c_21009])).

cnf(c_62,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_63,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_64,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_65,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_59,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_66,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_58,negated_conjecture,
    ( m1_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_67,plain,
    ( m1_pre_topc(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_68,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( m1_pre_topc(sK10,sK8) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_69,plain,
    ( m1_pre_topc(sK10,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_21115,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
    | k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21022,c_63,c_64,c_65,c_66,c_67,c_68,c_69])).

cnf(c_21116,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(renaming,[status(thm)],[c_21115])).

cnf(c_36,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11176,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | m1_subset_1(sK6(X0_57,X1_57,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))))) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_12487,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_subset_1(sK6(X0_57,X1_57,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11176])).

cnf(c_32,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ r3_tsep_1(X0,X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f86])).

cnf(c_1026,plain,
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
    inference(resolution,[status(thm)],[c_32,c_29])).

cnf(c_33,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1030,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_33,c_32,c_29])).

cnf(c_1031,plain,
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
    inference(renaming,[status(thm)],[c_1030])).

cnf(c_11146,plain,
    ( ~ r3_tsep_1(X0_57,X1_57,X2_57)
    | ~ v5_pre_topc(X0_58,X2_57,X3_57)
    | ~ v5_pre_topc(X1_58,X1_57,X3_57)
    | v5_pre_topc(k10_tmap_1(X0_57,X3_57,X1_57,X2_57,X1_58,X0_58),k1_tsep_1(X0_57,X1_57,X2_57),X3_57)
    | ~ v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X3_57))
    | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X3_57))
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X3_57))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X3_57))))
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(X3_57)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(X3_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_58)
    | ~ v1_funct_1(X1_58) ),
    inference(subtyping,[status(esa)],[c_1031])).

cnf(c_12517,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
    | v5_pre_topc(X0_58,X2_57,X3_57) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X3_57) != iProver_top
    | v5_pre_topc(k10_tmap_1(X0_57,X3_57,X1_57,X2_57,X1_58,X0_58),k1_tsep_1(X0_57,X1_57,X2_57),X3_57) = iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X3_57)) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X3_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X3_57)))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X3_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11146])).

cnf(c_3,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_11198,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57))
    | v1_funct_2(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ v2_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ l1_pre_topc(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_58)
    | ~ v1_funct_1(X1_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_12465,plain,
    ( v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57)) = iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11198])).

cnf(c_2,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_11199,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | m1_subset_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57))))
    | ~ v2_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ l1_pre_topc(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_58)
    | ~ v1_funct_1(X1_58) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_12464,plain,
    ( v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57)))) = iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11199])).

cnf(c_45,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_11167,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | ~ v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57)
    | ~ v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))
    | ~ m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))))
    | ~ v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_12496,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11167])).

cnf(c_14011,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top
    | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12464,c_12496])).

cnf(c_46,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_11166,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_11274,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11166])).

cnf(c_48,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_11164,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_11280,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11164])).

cnf(c_49,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_11163,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_11283,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11163])).

cnf(c_18796,plain,
    ( v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14011,c_11274,c_11280,c_11283])).

cnf(c_18797,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top ),
    inference(renaming,[status(thm)],[c_18796])).

cnf(c_12497,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11166])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_11197,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ v2_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ l1_pre_topc(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_58)
    | ~ v1_funct_1(X1_58)
    | v1_funct_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_12466,plain,
    ( v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11197])).

cnf(c_14738,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X4_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X5_57) != iProver_top
    | m1_pre_topc(X4_57,X5_57) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X5_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X5_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X4_57) = iProver_top
    | v2_struct_0(X5_57) = iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X5_57,X0_57,X4_57,X1_57,X1_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) = iProver_top
    | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_12466])).

cnf(c_18124,plain,
    ( v1_funct_1(k10_tmap_1(X5_57,X0_57,X4_57,X1_57,X1_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) = iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v2_struct_0(X5_57) = iProver_top
    | v2_struct_0(X4_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X5_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X5_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_57),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(X4_57,X5_57) != iProver_top
    | m1_pre_topc(X1_57,X5_57) != iProver_top
    | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X4_57),u1_struct_0(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14738,c_11280,c_11283])).

cnf(c_18125,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X4_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X5_57) != iProver_top
    | m1_pre_topc(X4_57,X5_57) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X5_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X5_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X4_57) = iProver_top
    | v2_struct_0(X5_57) = iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X5_57,X0_57,X4_57,X1_57,X1_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) = iProver_top ),
    inference(renaming,[status(thm)],[c_18124])).

cnf(c_18819,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18797,c_18125])).

cnf(c_18824,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12465,c_18819])).

cnf(c_18865,plain,
    ( v1_funct_1(X0_58) != iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18824,c_11274,c_11280,c_11283])).

cnf(c_18866,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_18865])).

cnf(c_18886,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | r3_tsep_1(X3_57,X2_57,X1_57) != iProver_top
    | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
    | v5_pre_topc(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),X1_57,X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12517,c_18866])).

cnf(c_47,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_11165,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | v5_pre_topc(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_47])).

cnf(c_11277,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | v5_pre_topc(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),X1_57,X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11165])).

cnf(c_19000,plain,
    ( v1_funct_1(X0_58) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | r3_tsep_1(X3_57,X2_57,X1_57) != iProver_top
    | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18886,c_11274,c_11277,c_11280,c_11283])).

cnf(c_19001,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
    | r3_tsep_1(X3_57,X2_57,X1_57) != iProver_top
    | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X1_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_19000])).

cnf(c_19024,plain,
    ( sP1(sK5(X0_57,X1_57,X2_57),X3_57,X1_57,X4_57,sK6(X0_57,X1_57,X2_57)) = iProver_top
    | sP2(X0_57,X1_57,X2_57) = iProver_top
    | r3_tsep_1(X4_57,X1_57,X3_57) != iProver_top
    | v5_pre_topc(sK6(X0_57,X1_57,X2_57),X1_57,sK5(X0_57,X1_57,X2_57)) != iProver_top
    | v1_funct_2(sK6(X0_57,X1_57,X2_57),u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))) != iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X3_57,X4_57) != iProver_top
    | m1_pre_topc(X1_57,X4_57) != iProver_top
    | v2_pre_topc(X4_57) != iProver_top
    | v2_pre_topc(sK5(X0_57,X1_57,X2_57)) != iProver_top
    | l1_pre_topc(X4_57) != iProver_top
    | l1_pre_topc(sK5(X0_57,X1_57,X2_57)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X4_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(sK5(X0_57,X1_57,X2_57)) = iProver_top
    | v1_funct_1(sK6(X0_57,X1_57,X2_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12487,c_19001])).

cnf(c_37,plain,
    ( sP2(X0,X1,X2)
    | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_11175,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | v5_pre_topc(sK6(X0_57,X1_57,X2_57),X1_57,sK5(X0_57,X1_57,X2_57))
    | ~ r1_tsep_1(X1_57,X2_57) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_11261,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | v5_pre_topc(sK6(X0_57,X1_57,X2_57),X1_57,sK5(X0_57,X1_57,X2_57)) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11175])).

cnf(c_38,plain,
    ( sP2(X0,X1,X2)
    | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_11174,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | v1_funct_2(sK6(X0_57,X1_57,X2_57),u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57)))
    | ~ r1_tsep_1(X1_57,X2_57) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_11262,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | v1_funct_2(sK6(X0_57,X1_57,X2_57),u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11174])).

cnf(c_39,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | v1_funct_1(sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11173,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | v1_funct_1(sK6(X0_57,X1_57,X2_57)) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_11263,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | v1_funct_1(sK6(X0_57,X1_57,X2_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11173])).

cnf(c_40,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | l1_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_11172,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | l1_pre_topc(sK5(X0_57,X1_57,X2_57)) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_11264,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | l1_pre_topc(sK5(X0_57,X1_57,X2_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11172])).

cnf(c_41,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | v2_pre_topc(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_11171,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | v2_pre_topc(sK5(X0_57,X1_57,X2_57)) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_11265,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | v2_pre_topc(sK5(X0_57,X1_57,X2_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11171])).

cnf(c_42,plain,
    ( sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ v2_struct_0(sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_11170,plain,
    ( sP2(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57)
    | ~ v2_struct_0(sK5(X0_57,X1_57,X2_57)) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_11266,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | v2_struct_0(sK5(X0_57,X1_57,X2_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11170])).

cnf(c_19374,plain,
    ( l1_pre_topc(X4_57) != iProver_top
    | sP1(sK5(X0_57,X1_57,X2_57),X3_57,X1_57,X4_57,sK6(X0_57,X1_57,X2_57)) = iProver_top
    | sP2(X0_57,X1_57,X2_57) = iProver_top
    | r3_tsep_1(X4_57,X1_57,X3_57) != iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X3_57,X4_57) != iProver_top
    | m1_pre_topc(X1_57,X4_57) != iProver_top
    | v2_pre_topc(X4_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X4_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19024,c_11261,c_11262,c_11263,c_11264,c_11265,c_11266])).

cnf(c_19375,plain,
    ( sP1(sK5(X0_57,X1_57,X2_57),X3_57,X1_57,X4_57,sK6(X0_57,X1_57,X2_57)) = iProver_top
    | sP2(X0_57,X1_57,X2_57) = iProver_top
    | r3_tsep_1(X4_57,X1_57,X3_57) != iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X3_57,X4_57) != iProver_top
    | m1_pre_topc(X1_57,X4_57) != iProver_top
    | v2_pre_topc(X4_57) != iProver_top
    | l1_pre_topc(X4_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X4_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_19374])).

cnf(c_35,plain,
    ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
    | sP2(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_11177,plain,
    ( ~ sP1(sK5(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57,sK6(X0_57,X1_57,X2_57))
    | sP2(X0_57,X1_57,X2_57)
    | ~ r1_tsep_1(X1_57,X2_57) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_12486,plain,
    ( sP1(sK5(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57,sK6(X0_57,X1_57,X2_57)) != iProver_top
    | sP2(X0_57,X1_57,X2_57) = iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11177])).

cnf(c_19391,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
    | r1_tsep_1(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_19375,c_12486])).

cnf(c_11179,plain,
    ( ~ r3_tsep_1(X0_57,X1_57,X2_57)
    | r1_tsep_1(X1_57,X2_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_11255,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
    | r1_tsep_1(X1_57,X2_57) = iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11179])).

cnf(c_19396,plain,
    ( r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
    | sP2(X0_57,X1_57,X2_57) = iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19391,c_11255])).

cnf(c_19397,plain,
    ( sP2(X0_57,X1_57,X2_57) = iProver_top
    | r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_19396])).

cnf(c_21121,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
    | sP2(sK8,sK9,sK10) = iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_21116,c_19397])).

cnf(c_54,negated_conjecture,
    ( ~ sP2(sK8,sK9,sK10)
    | ~ r3_tsep_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_71,plain,
    ( sP2(sK8,sK9,sK10) != iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_21148,plain,
    ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21121,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_71,c_21116])).

cnf(c_16028,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | sP1(X0_57,X4_57,k1_tsep_1(X3_57,X2_57,X1_57),X5_57,k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top
    | sP2(X5_57,k1_tsep_1(X3_57,X2_57,X1_57),X4_57) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12501,c_12494])).

cnf(c_51,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X5,X1,X0)
    | v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_11161,plain,
    ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
    | ~ v5_pre_topc(X1_58,X1_57,X0_57)
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57)
    | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | ~ v1_funct_1(X1_58) ),
    inference(subtyping,[status(esa)],[c_51])).

cnf(c_11289,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) = iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11161])).

cnf(c_11292,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11160])).

cnf(c_11295,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11159])).

cnf(c_18146,plain,
    ( v1_funct_1(X1_58) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | sP2(X5_57,k1_tsep_1(X3_57,X2_57,X1_57),X4_57) != iProver_top
    | sP1(X0_57,X4_57,k1_tsep_1(X3_57,X2_57,X1_57),X5_57,k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top
    | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16028,c_11289,c_11292,c_11295])).

cnf(c_18147,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | sP1(X0_57,X4_57,k1_tsep_1(X3_57,X2_57,X1_57),X5_57,k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top
    | sP2(X5_57,k1_tsep_1(X3_57,X2_57,X1_57),X4_57) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_18146])).

cnf(c_21154,plain,
    ( sP1(sK4(sK8,sK9,sK10),X0_57,k1_tsep_1(sK8,sK9,sK10),X1_57,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)) = iProver_top
    | sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | sP2(X1_57,k1_tsep_1(sK8,sK9,sK10),X0_57) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21148,c_18147])).

cnf(c_22519,plain,
    ( sP1(sK4(sK8,sK9,sK10),X0_57,k1_tsep_1(sK8,sK9,sK10),X1_57,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)) = iProver_top
    | sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | sP2(X1_57,k1_tsep_1(sK8,sK9,sK10),X0_57) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12467,c_21154])).

cnf(c_70,plain,
    ( sP2(sK8,sK9,sK10) = iProver_top
    | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_25,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ r3_tsep_1(X3,X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11180,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | ~ r3_tsep_1(X3_57,X2_57,X1_57)
    | ~ m1_pre_topc(X1_57,X3_57)
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(X3_57)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(X3_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_13503,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
    | ~ r3_tsep_1(X0_57,sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_57)
    | ~ m1_pre_topc(sK9,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(sK4(X0_57,sK9,sK10))
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK4(X0_57,sK9,sK10))
    | v2_struct_0(X0_57)
    | v2_struct_0(sK4(X0_57,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_11180])).

cnf(c_13504,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
    | r3_tsep_1(X0_57,sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_57) != iProver_top
    | m1_pre_topc(sK9,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK4(X0_57,sK9,sK10)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK4(X0_57,sK9,sK10)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK4(X0_57,sK9,sK10)) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13503])).

cnf(c_13506,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | r3_tsep_1(sK8,sK9,sK10) != iProver_top
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
    inference(instantiation,[status(thm)],[c_13504])).

cnf(c_12502,plain,
    ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
    | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) = iProver_top
    | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11161])).

cnf(c_21159,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21148,c_12502])).

cnf(c_21920,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12467,c_21159])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_399,plain,
    ( ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | sP0(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_16,c_15,c_14])).

cnf(c_400,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_11149,plain,
    ( sP0(X0_57,X1_57,X2_57,X3_57)
    | ~ v5_pre_topc(sK3(X0_57,X1_57,X2_57,X3_57),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_13501,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
    | ~ v5_pre_topc(sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57),k1_tsep_1(X0_57,sK9,sK10),sK4(X0_57,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_11149])).

cnf(c_13512,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
    | v5_pre_topc(sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57),k1_tsep_1(X0_57,sK9,sK10),sK4(X0_57,sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13501])).

cnf(c_13514,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13512])).

cnf(c_13497,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
    | v1_funct_1(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57))) ),
    inference(instantiation,[status(thm)],[c_11193])).

cnf(c_13528,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
    | v1_funct_1(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13497])).

cnf(c_13530,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13528])).

cnf(c_13493,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
    | v1_funct_2(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),u1_struct_0(sK10),u1_struct_0(sK4(X0_57,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_11194])).

cnf(c_13544,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),u1_struct_0(sK10),u1_struct_0(sK4(X0_57,sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13493])).

cnf(c_13546,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13544])).

cnf(c_13492,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
    | v5_pre_topc(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),sK10,sK4(X0_57,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_11195])).

cnf(c_13548,plain,
    ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),sK10,sK4(X0_57,sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13492])).

cnf(c_13550,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13548])).

cnf(c_22733,plain,
    ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
    | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21920,c_13514,c_13530,c_13546,c_13550])).

cnf(c_22740,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | sP2(sK8,sK9,sK10) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17825,c_22733])).

cnf(c_22770,plain,
    ( v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22519,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_13506,c_22740])).

cnf(c_22771,plain,
    ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
    | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
    | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_22770])).

cnf(c_22778,plain,
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
    inference(superposition,[status(thm)],[c_22771,c_12479])).

cnf(c_26,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_490,plain,
    ( sP2(sK8,sK9,sK10)
    | r3_tsep_1(sK8,sK9,sK10) ),
    inference(prop_impl,[status(thm)],[c_55])).

cnf(c_5916,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_490])).

cnf(c_5917,plain,
    ( sP2(sK8,sK9,sK10)
    | r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,sK8)
    | ~ m1_pre_topc(sK9,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_5916])).

cnf(c_1573,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | r1_tsep_1(X0,X1)
    | sK10 != X1
    | sK9 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_490])).

cnf(c_1574,plain,
    ( r3_tsep_1(sK8,sK9,sK10)
    | r1_tsep_1(sK9,sK10) ),
    inference(unflattening,[status(thm)],[c_1573])).

cnf(c_5919,plain,
    ( r1_tsep_1(sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5917,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_54,c_1574])).

cnf(c_5921,plain,
    ( r1_tsep_1(sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5919])).

cnf(c_13259,plain,
    ( r3_tsep_1(X0_57,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_57)
    | ~ m1_pre_topc(sK9,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ v2_struct_0(sK4(X0_57,sK9,sK10))
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_11181])).

cnf(c_13300,plain,
    ( r3_tsep_1(X0_57,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_57) != iProver_top
    | m1_pre_topc(sK9,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK4(X0_57,sK9,sK10)) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13259])).

cnf(c_13302,plain,
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
    inference(instantiation,[status(thm)],[c_13300])).

cnf(c_13258,plain,
    ( r3_tsep_1(X0_57,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_57)
    | ~ m1_pre_topc(sK9,X0_57)
    | ~ v2_pre_topc(X0_57)
    | v2_pre_topc(sK4(X0_57,sK9,sK10))
    | ~ l1_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_11182])).

cnf(c_13304,plain,
    ( r3_tsep_1(X0_57,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_57) != iProver_top
    | m1_pre_topc(sK9,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK4(X0_57,sK9,sK10)) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13258])).

cnf(c_13306,plain,
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
    inference(instantiation,[status(thm)],[c_13304])).

cnf(c_13257,plain,
    ( r3_tsep_1(X0_57,sK9,sK10)
    | ~ r1_tsep_1(sK9,sK10)
    | ~ m1_pre_topc(sK10,X0_57)
    | ~ m1_pre_topc(sK9,X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | l1_pre_topc(sK4(X0_57,sK9,sK10))
    | v2_struct_0(X0_57)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_11183])).

cnf(c_13308,plain,
    ( r3_tsep_1(X0_57,sK9,sK10) = iProver_top
    | r1_tsep_1(sK9,sK10) != iProver_top
    | m1_pre_topc(sK10,X0_57) != iProver_top
    | m1_pre_topc(sK9,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK4(X0_57,sK9,sK10)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13257])).

cnf(c_13310,plain,
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
    inference(instantiation,[status(thm)],[c_13308])).

cnf(c_22948,plain,
    ( r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22778,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_5921,c_13302,c_13306,c_13310])).

cnf(c_22953,plain,
    ( sP2(sK8,sK9,sK10) = iProver_top
    | m1_pre_topc(sK10,sK8) != iProver_top
    | m1_pre_topc(sK9,sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_22948,c_19397])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22953,c_22948,c_71,c_69,c_68,c_67,c_66,c_65,c_64,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.49/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.50  
% 7.49/1.50  ------  iProver source info
% 7.49/1.50  
% 7.49/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.50  git: non_committed_changes: false
% 7.49/1.50  git: last_make_outside_of_git: false
% 7.49/1.50  
% 7.49/1.50  ------ 
% 7.49/1.50  
% 7.49/1.50  ------ Input Options
% 7.49/1.50  
% 7.49/1.50  --out_options                           all
% 7.49/1.50  --tptp_safe_out                         true
% 7.49/1.50  --problem_path                          ""
% 7.49/1.50  --include_path                          ""
% 7.49/1.50  --clausifier                            res/vclausify_rel
% 7.49/1.50  --clausifier_options                    --mode clausify
% 7.49/1.50  --stdin                                 false
% 7.49/1.50  --stats_out                             all
% 7.49/1.50  
% 7.49/1.50  ------ General Options
% 7.49/1.50  
% 7.49/1.50  --fof                                   false
% 7.49/1.50  --time_out_real                         305.
% 7.49/1.50  --time_out_virtual                      -1.
% 7.49/1.50  --symbol_type_check                     false
% 7.49/1.50  --clausify_out                          false
% 7.49/1.50  --sig_cnt_out                           false
% 7.49/1.50  --trig_cnt_out                          false
% 7.49/1.50  --trig_cnt_out_tolerance                1.
% 7.49/1.50  --trig_cnt_out_sk_spl                   false
% 7.49/1.50  --abstr_cl_out                          false
% 7.49/1.50  
% 7.49/1.50  ------ Global Options
% 7.49/1.50  
% 7.49/1.50  --schedule                              default
% 7.49/1.50  --add_important_lit                     false
% 7.49/1.50  --prop_solver_per_cl                    1000
% 7.49/1.50  --min_unsat_core                        false
% 7.49/1.50  --soft_assumptions                      false
% 7.49/1.50  --soft_lemma_size                       3
% 7.49/1.50  --prop_impl_unit_size                   0
% 7.49/1.50  --prop_impl_unit                        []
% 7.49/1.50  --share_sel_clauses                     true
% 7.49/1.50  --reset_solvers                         false
% 7.49/1.50  --bc_imp_inh                            [conj_cone]
% 7.49/1.50  --conj_cone_tolerance                   3.
% 7.49/1.50  --extra_neg_conj                        none
% 7.49/1.50  --large_theory_mode                     true
% 7.49/1.50  --prolific_symb_bound                   200
% 7.49/1.50  --lt_threshold                          2000
% 7.49/1.50  --clause_weak_htbl                      true
% 7.49/1.50  --gc_record_bc_elim                     false
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing Options
% 7.49/1.50  
% 7.49/1.50  --preprocessing_flag                    true
% 7.49/1.50  --time_out_prep_mult                    0.1
% 7.49/1.50  --splitting_mode                        input
% 7.49/1.50  --splitting_grd                         true
% 7.49/1.50  --splitting_cvd                         false
% 7.49/1.50  --splitting_cvd_svl                     false
% 7.49/1.50  --splitting_nvd                         32
% 7.49/1.50  --sub_typing                            true
% 7.49/1.50  --prep_gs_sim                           true
% 7.49/1.50  --prep_unflatten                        true
% 7.49/1.50  --prep_res_sim                          true
% 7.49/1.50  --prep_upred                            true
% 7.49/1.50  --prep_sem_filter                       exhaustive
% 7.49/1.50  --prep_sem_filter_out                   false
% 7.49/1.50  --pred_elim                             true
% 7.49/1.50  --res_sim_input                         true
% 7.49/1.50  --eq_ax_congr_red                       true
% 7.49/1.50  --pure_diseq_elim                       true
% 7.49/1.50  --brand_transform                       false
% 7.49/1.50  --non_eq_to_eq                          false
% 7.49/1.50  --prep_def_merge                        true
% 7.49/1.50  --prep_def_merge_prop_impl              false
% 7.49/1.50  --prep_def_merge_mbd                    true
% 7.49/1.50  --prep_def_merge_tr_red                 false
% 7.49/1.50  --prep_def_merge_tr_cl                  false
% 7.49/1.50  --smt_preprocessing                     true
% 7.49/1.50  --smt_ac_axioms                         fast
% 7.49/1.50  --preprocessed_out                      false
% 7.49/1.50  --preprocessed_stats                    false
% 7.49/1.50  
% 7.49/1.50  ------ Abstraction refinement Options
% 7.49/1.50  
% 7.49/1.50  --abstr_ref                             []
% 7.49/1.50  --abstr_ref_prep                        false
% 7.49/1.50  --abstr_ref_until_sat                   false
% 7.49/1.50  --abstr_ref_sig_restrict                funpre
% 7.49/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.50  --abstr_ref_under                       []
% 7.49/1.50  
% 7.49/1.50  ------ SAT Options
% 7.49/1.50  
% 7.49/1.50  --sat_mode                              false
% 7.49/1.50  --sat_fm_restart_options                ""
% 7.49/1.50  --sat_gr_def                            false
% 7.49/1.50  --sat_epr_types                         true
% 7.49/1.50  --sat_non_cyclic_types                  false
% 7.49/1.50  --sat_finite_models                     false
% 7.49/1.50  --sat_fm_lemmas                         false
% 7.49/1.50  --sat_fm_prep                           false
% 7.49/1.50  --sat_fm_uc_incr                        true
% 7.49/1.50  --sat_out_model                         small
% 7.49/1.50  --sat_out_clauses                       false
% 7.49/1.50  
% 7.49/1.50  ------ QBF Options
% 7.49/1.50  
% 7.49/1.50  --qbf_mode                              false
% 7.49/1.50  --qbf_elim_univ                         false
% 7.49/1.50  --qbf_dom_inst                          none
% 7.49/1.50  --qbf_dom_pre_inst                      false
% 7.49/1.50  --qbf_sk_in                             false
% 7.49/1.50  --qbf_pred_elim                         true
% 7.49/1.50  --qbf_split                             512
% 7.49/1.50  
% 7.49/1.50  ------ BMC1 Options
% 7.49/1.50  
% 7.49/1.50  --bmc1_incremental                      false
% 7.49/1.50  --bmc1_axioms                           reachable_all
% 7.49/1.50  --bmc1_min_bound                        0
% 7.49/1.50  --bmc1_max_bound                        -1
% 7.49/1.50  --bmc1_max_bound_default                -1
% 7.49/1.50  --bmc1_symbol_reachability              true
% 7.49/1.50  --bmc1_property_lemmas                  false
% 7.49/1.50  --bmc1_k_induction                      false
% 7.49/1.50  --bmc1_non_equiv_states                 false
% 7.49/1.50  --bmc1_deadlock                         false
% 7.49/1.50  --bmc1_ucm                              false
% 7.49/1.50  --bmc1_add_unsat_core                   none
% 7.49/1.50  --bmc1_unsat_core_children              false
% 7.49/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.50  --bmc1_out_stat                         full
% 7.49/1.50  --bmc1_ground_init                      false
% 7.49/1.50  --bmc1_pre_inst_next_state              false
% 7.49/1.50  --bmc1_pre_inst_state                   false
% 7.49/1.50  --bmc1_pre_inst_reach_state             false
% 7.49/1.50  --bmc1_out_unsat_core                   false
% 7.49/1.50  --bmc1_aig_witness_out                  false
% 7.49/1.50  --bmc1_verbose                          false
% 7.49/1.50  --bmc1_dump_clauses_tptp                false
% 7.49/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.50  --bmc1_dump_file                        -
% 7.49/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.50  --bmc1_ucm_extend_mode                  1
% 7.49/1.50  --bmc1_ucm_init_mode                    2
% 7.49/1.50  --bmc1_ucm_cone_mode                    none
% 7.49/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.50  --bmc1_ucm_relax_model                  4
% 7.49/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.50  --bmc1_ucm_layered_model                none
% 7.49/1.50  --bmc1_ucm_max_lemma_size               10
% 7.49/1.50  
% 7.49/1.50  ------ AIG Options
% 7.49/1.50  
% 7.49/1.50  --aig_mode                              false
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation Options
% 7.49/1.50  
% 7.49/1.50  --instantiation_flag                    true
% 7.49/1.50  --inst_sos_flag                         false
% 7.49/1.50  --inst_sos_phase                        true
% 7.49/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel_side                     num_symb
% 7.49/1.50  --inst_solver_per_active                1400
% 7.49/1.50  --inst_solver_calls_frac                1.
% 7.49/1.50  --inst_passive_queue_type               priority_queues
% 7.49/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.50  --inst_passive_queues_freq              [25;2]
% 7.49/1.50  --inst_dismatching                      true
% 7.49/1.50  --inst_eager_unprocessed_to_passive     true
% 7.49/1.50  --inst_prop_sim_given                   true
% 7.49/1.50  --inst_prop_sim_new                     false
% 7.49/1.50  --inst_subs_new                         false
% 7.49/1.50  --inst_eq_res_simp                      false
% 7.49/1.50  --inst_subs_given                       false
% 7.49/1.50  --inst_orphan_elimination               true
% 7.49/1.50  --inst_learning_loop_flag               true
% 7.49/1.50  --inst_learning_start                   3000
% 7.49/1.50  --inst_learning_factor                  2
% 7.49/1.50  --inst_start_prop_sim_after_learn       3
% 7.49/1.50  --inst_sel_renew                        solver
% 7.49/1.50  --inst_lit_activity_flag                true
% 7.49/1.50  --inst_restr_to_given                   false
% 7.49/1.50  --inst_activity_threshold               500
% 7.49/1.50  --inst_out_proof                        true
% 7.49/1.50  
% 7.49/1.50  ------ Resolution Options
% 7.49/1.50  
% 7.49/1.50  --resolution_flag                       true
% 7.49/1.50  --res_lit_sel                           adaptive
% 7.49/1.50  --res_lit_sel_side                      none
% 7.49/1.50  --res_ordering                          kbo
% 7.49/1.50  --res_to_prop_solver                    active
% 7.49/1.50  --res_prop_simpl_new                    false
% 7.49/1.50  --res_prop_simpl_given                  true
% 7.49/1.50  --res_passive_queue_type                priority_queues
% 7.49/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.50  --res_passive_queues_freq               [15;5]
% 7.49/1.50  --res_forward_subs                      full
% 7.49/1.50  --res_backward_subs                     full
% 7.49/1.50  --res_forward_subs_resolution           true
% 7.49/1.50  --res_backward_subs_resolution          true
% 7.49/1.50  --res_orphan_elimination                true
% 7.49/1.50  --res_time_limit                        2.
% 7.49/1.50  --res_out_proof                         true
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Options
% 7.49/1.50  
% 7.49/1.50  --superposition_flag                    true
% 7.49/1.50  --sup_passive_queue_type                priority_queues
% 7.49/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.50  --demod_completeness_check              fast
% 7.49/1.50  --demod_use_ground                      true
% 7.49/1.50  --sup_to_prop_solver                    passive
% 7.49/1.50  --sup_prop_simpl_new                    true
% 7.49/1.50  --sup_prop_simpl_given                  true
% 7.49/1.50  --sup_fun_splitting                     false
% 7.49/1.50  --sup_smt_interval                      50000
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Simplification Setup
% 7.49/1.50  
% 7.49/1.50  --sup_indices_passive                   []
% 7.49/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_full_bw                           [BwDemod]
% 7.49/1.50  --sup_immed_triv                        [TrivRules]
% 7.49/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_immed_bw_main                     []
% 7.49/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  
% 7.49/1.50  ------ Combination Options
% 7.49/1.50  
% 7.49/1.50  --comb_res_mult                         3
% 7.49/1.50  --comb_sup_mult                         2
% 7.49/1.50  --comb_inst_mult                        10
% 7.49/1.50  
% 7.49/1.50  ------ Debug Options
% 7.49/1.50  
% 7.49/1.50  --dbg_backtrace                         false
% 7.49/1.50  --dbg_dump_prop_clauses                 false
% 7.49/1.50  --dbg_dump_prop_clauses_file            -
% 7.49/1.50  --dbg_out_stat                          false
% 7.49/1.50  ------ Parsing...
% 7.49/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  ------ Proving...
% 7.49/1.50  ------ Problem Properties 
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  clauses                                 57
% 7.49/1.50  conjectures                             9
% 7.49/1.50  EPR                                     12
% 7.49/1.50  Horn                                    20
% 7.49/1.50  unary                                   7
% 7.49/1.50  binary                                  19
% 7.49/1.50  lits                                    338
% 7.49/1.50  lits eq                                 1
% 7.49/1.50  fd_pure                                 0
% 7.49/1.50  fd_pseudo                               0
% 7.49/1.50  fd_cond                                 0
% 7.49/1.50  fd_pseudo_cond                          1
% 7.49/1.50  AC symbols                              0
% 7.49/1.50  
% 7.49/1.50  ------ Schedule dynamic 5 is on 
% 7.49/1.50  
% 7.49/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ 
% 7.49/1.50  Current options:
% 7.49/1.50  ------ 
% 7.49/1.50  
% 7.49/1.50  ------ Input Options
% 7.49/1.50  
% 7.49/1.50  --out_options                           all
% 7.49/1.50  --tptp_safe_out                         true
% 7.49/1.50  --problem_path                          ""
% 7.49/1.50  --include_path                          ""
% 7.49/1.50  --clausifier                            res/vclausify_rel
% 7.49/1.50  --clausifier_options                    --mode clausify
% 7.49/1.50  --stdin                                 false
% 7.49/1.50  --stats_out                             all
% 7.49/1.50  
% 7.49/1.50  ------ General Options
% 7.49/1.50  
% 7.49/1.50  --fof                                   false
% 7.49/1.50  --time_out_real                         305.
% 7.49/1.50  --time_out_virtual                      -1.
% 7.49/1.50  --symbol_type_check                     false
% 7.49/1.50  --clausify_out                          false
% 7.49/1.50  --sig_cnt_out                           false
% 7.49/1.50  --trig_cnt_out                          false
% 7.49/1.50  --trig_cnt_out_tolerance                1.
% 7.49/1.50  --trig_cnt_out_sk_spl                   false
% 7.49/1.50  --abstr_cl_out                          false
% 7.49/1.50  
% 7.49/1.50  ------ Global Options
% 7.49/1.50  
% 7.49/1.50  --schedule                              default
% 7.49/1.50  --add_important_lit                     false
% 7.49/1.50  --prop_solver_per_cl                    1000
% 7.49/1.50  --min_unsat_core                        false
% 7.49/1.50  --soft_assumptions                      false
% 7.49/1.50  --soft_lemma_size                       3
% 7.49/1.50  --prop_impl_unit_size                   0
% 7.49/1.50  --prop_impl_unit                        []
% 7.49/1.50  --share_sel_clauses                     true
% 7.49/1.50  --reset_solvers                         false
% 7.49/1.50  --bc_imp_inh                            [conj_cone]
% 7.49/1.50  --conj_cone_tolerance                   3.
% 7.49/1.50  --extra_neg_conj                        none
% 7.49/1.50  --large_theory_mode                     true
% 7.49/1.50  --prolific_symb_bound                   200
% 7.49/1.50  --lt_threshold                          2000
% 7.49/1.50  --clause_weak_htbl                      true
% 7.49/1.50  --gc_record_bc_elim                     false
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing Options
% 7.49/1.50  
% 7.49/1.50  --preprocessing_flag                    true
% 7.49/1.50  --time_out_prep_mult                    0.1
% 7.49/1.50  --splitting_mode                        input
% 7.49/1.50  --splitting_grd                         true
% 7.49/1.50  --splitting_cvd                         false
% 7.49/1.50  --splitting_cvd_svl                     false
% 7.49/1.50  --splitting_nvd                         32
% 7.49/1.50  --sub_typing                            true
% 7.49/1.50  --prep_gs_sim                           true
% 7.49/1.50  --prep_unflatten                        true
% 7.49/1.50  --prep_res_sim                          true
% 7.49/1.50  --prep_upred                            true
% 7.49/1.50  --prep_sem_filter                       exhaustive
% 7.49/1.50  --prep_sem_filter_out                   false
% 7.49/1.50  --pred_elim                             true
% 7.49/1.50  --res_sim_input                         true
% 7.49/1.50  --eq_ax_congr_red                       true
% 7.49/1.50  --pure_diseq_elim                       true
% 7.49/1.50  --brand_transform                       false
% 7.49/1.50  --non_eq_to_eq                          false
% 7.49/1.50  --prep_def_merge                        true
% 7.49/1.50  --prep_def_merge_prop_impl              false
% 7.49/1.50  --prep_def_merge_mbd                    true
% 7.49/1.50  --prep_def_merge_tr_red                 false
% 7.49/1.50  --prep_def_merge_tr_cl                  false
% 7.49/1.50  --smt_preprocessing                     true
% 7.49/1.50  --smt_ac_axioms                         fast
% 7.49/1.50  --preprocessed_out                      false
% 7.49/1.50  --preprocessed_stats                    false
% 7.49/1.50  
% 7.49/1.50  ------ Abstraction refinement Options
% 7.49/1.50  
% 7.49/1.50  --abstr_ref                             []
% 7.49/1.50  --abstr_ref_prep                        false
% 7.49/1.50  --abstr_ref_until_sat                   false
% 7.49/1.50  --abstr_ref_sig_restrict                funpre
% 7.49/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.50  --abstr_ref_under                       []
% 7.49/1.50  
% 7.49/1.50  ------ SAT Options
% 7.49/1.50  
% 7.49/1.50  --sat_mode                              false
% 7.49/1.50  --sat_fm_restart_options                ""
% 7.49/1.50  --sat_gr_def                            false
% 7.49/1.50  --sat_epr_types                         true
% 7.49/1.50  --sat_non_cyclic_types                  false
% 7.49/1.50  --sat_finite_models                     false
% 7.49/1.50  --sat_fm_lemmas                         false
% 7.49/1.50  --sat_fm_prep                           false
% 7.49/1.50  --sat_fm_uc_incr                        true
% 7.49/1.50  --sat_out_model                         small
% 7.49/1.50  --sat_out_clauses                       false
% 7.49/1.50  
% 7.49/1.50  ------ QBF Options
% 7.49/1.50  
% 7.49/1.50  --qbf_mode                              false
% 7.49/1.50  --qbf_elim_univ                         false
% 7.49/1.50  --qbf_dom_inst                          none
% 7.49/1.50  --qbf_dom_pre_inst                      false
% 7.49/1.50  --qbf_sk_in                             false
% 7.49/1.50  --qbf_pred_elim                         true
% 7.49/1.50  --qbf_split                             512
% 7.49/1.50  
% 7.49/1.50  ------ BMC1 Options
% 7.49/1.50  
% 7.49/1.50  --bmc1_incremental                      false
% 7.49/1.50  --bmc1_axioms                           reachable_all
% 7.49/1.50  --bmc1_min_bound                        0
% 7.49/1.50  --bmc1_max_bound                        -1
% 7.49/1.50  --bmc1_max_bound_default                -1
% 7.49/1.50  --bmc1_symbol_reachability              true
% 7.49/1.50  --bmc1_property_lemmas                  false
% 7.49/1.50  --bmc1_k_induction                      false
% 7.49/1.50  --bmc1_non_equiv_states                 false
% 7.49/1.50  --bmc1_deadlock                         false
% 7.49/1.50  --bmc1_ucm                              false
% 7.49/1.50  --bmc1_add_unsat_core                   none
% 7.49/1.50  --bmc1_unsat_core_children              false
% 7.49/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.50  --bmc1_out_stat                         full
% 7.49/1.50  --bmc1_ground_init                      false
% 7.49/1.50  --bmc1_pre_inst_next_state              false
% 7.49/1.50  --bmc1_pre_inst_state                   false
% 7.49/1.50  --bmc1_pre_inst_reach_state             false
% 7.49/1.50  --bmc1_out_unsat_core                   false
% 7.49/1.50  --bmc1_aig_witness_out                  false
% 7.49/1.50  --bmc1_verbose                          false
% 7.49/1.50  --bmc1_dump_clauses_tptp                false
% 7.49/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.50  --bmc1_dump_file                        -
% 7.49/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.50  --bmc1_ucm_extend_mode                  1
% 7.49/1.50  --bmc1_ucm_init_mode                    2
% 7.49/1.50  --bmc1_ucm_cone_mode                    none
% 7.49/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.50  --bmc1_ucm_relax_model                  4
% 7.49/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.50  --bmc1_ucm_layered_model                none
% 7.49/1.50  --bmc1_ucm_max_lemma_size               10
% 7.49/1.50  
% 7.49/1.50  ------ AIG Options
% 7.49/1.50  
% 7.49/1.50  --aig_mode                              false
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation Options
% 7.49/1.50  
% 7.49/1.50  --instantiation_flag                    true
% 7.49/1.50  --inst_sos_flag                         false
% 7.49/1.50  --inst_sos_phase                        true
% 7.49/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel_side                     none
% 7.49/1.50  --inst_solver_per_active                1400
% 7.49/1.50  --inst_solver_calls_frac                1.
% 7.49/1.50  --inst_passive_queue_type               priority_queues
% 7.49/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.50  --inst_passive_queues_freq              [25;2]
% 7.49/1.50  --inst_dismatching                      true
% 7.49/1.50  --inst_eager_unprocessed_to_passive     true
% 7.49/1.50  --inst_prop_sim_given                   true
% 7.49/1.50  --inst_prop_sim_new                     false
% 7.49/1.50  --inst_subs_new                         false
% 7.49/1.50  --inst_eq_res_simp                      false
% 7.49/1.50  --inst_subs_given                       false
% 7.49/1.50  --inst_orphan_elimination               true
% 7.49/1.50  --inst_learning_loop_flag               true
% 7.49/1.50  --inst_learning_start                   3000
% 7.49/1.50  --inst_learning_factor                  2
% 7.49/1.50  --inst_start_prop_sim_after_learn       3
% 7.49/1.50  --inst_sel_renew                        solver
% 7.49/1.50  --inst_lit_activity_flag                true
% 7.49/1.50  --inst_restr_to_given                   false
% 7.49/1.50  --inst_activity_threshold               500
% 7.49/1.50  --inst_out_proof                        true
% 7.49/1.50  
% 7.49/1.50  ------ Resolution Options
% 7.49/1.50  
% 7.49/1.50  --resolution_flag                       false
% 7.49/1.50  --res_lit_sel                           adaptive
% 7.49/1.50  --res_lit_sel_side                      none
% 7.49/1.50  --res_ordering                          kbo
% 7.49/1.50  --res_to_prop_solver                    active
% 7.49/1.50  --res_prop_simpl_new                    false
% 7.49/1.50  --res_prop_simpl_given                  true
% 7.49/1.50  --res_passive_queue_type                priority_queues
% 7.49/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.50  --res_passive_queues_freq               [15;5]
% 7.49/1.50  --res_forward_subs                      full
% 7.49/1.50  --res_backward_subs                     full
% 7.49/1.50  --res_forward_subs_resolution           true
% 7.49/1.50  --res_backward_subs_resolution          true
% 7.49/1.50  --res_orphan_elimination                true
% 7.49/1.50  --res_time_limit                        2.
% 7.49/1.50  --res_out_proof                         true
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Options
% 7.49/1.50  
% 7.49/1.50  --superposition_flag                    true
% 7.49/1.50  --sup_passive_queue_type                priority_queues
% 7.49/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.50  --demod_completeness_check              fast
% 7.49/1.50  --demod_use_ground                      true
% 7.49/1.50  --sup_to_prop_solver                    passive
% 7.49/1.50  --sup_prop_simpl_new                    true
% 7.49/1.50  --sup_prop_simpl_given                  true
% 7.49/1.50  --sup_fun_splitting                     false
% 7.49/1.50  --sup_smt_interval                      50000
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Simplification Setup
% 7.49/1.50  
% 7.49/1.50  --sup_indices_passive                   []
% 7.49/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_full_bw                           [BwDemod]
% 7.49/1.50  --sup_immed_triv                        [TrivRules]
% 7.49/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_immed_bw_main                     []
% 7.49/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  
% 7.49/1.50  ------ Combination Options
% 7.49/1.50  
% 7.49/1.50  --comb_res_mult                         3
% 7.49/1.50  --comb_sup_mult                         2
% 7.49/1.50  --comb_inst_mult                        10
% 7.49/1.50  
% 7.49/1.50  ------ Debug Options
% 7.49/1.50  
% 7.49/1.50  --dbg_backtrace                         false
% 7.49/1.50  --dbg_dump_prop_clauses                 false
% 7.49/1.50  --dbg_dump_prop_clauses_file            -
% 7.49/1.50  --dbg_out_stat                          false
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS status Theorem for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  fof(f23,plain,(
% 7.49/1.50    ! [X3,X2,X1,X0] : (sP0(X3,X2,X1,X0) <=> ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)))),
% 7.49/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.49/1.50  
% 7.49/1.50  fof(f29,plain,(
% 7.49/1.50    ! [X3,X2,X1,X0] : ((sP0(X3,X2,X1,X0) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~sP0(X3,X2,X1,X0)))),
% 7.49/1.50    inference(nnf_transformation,[],[f23])).
% 7.49/1.50  
% 7.49/1.50  fof(f30,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 7.49/1.50    inference(rectify,[],[f29])).
% 7.49/1.50  
% 7.49/1.50  fof(f31,plain,(
% 7.49/1.50    ! [X3,X2,X1,X0] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) => ((~m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(sK3(X0,X1,X2,X3))))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f32,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(sK3(X0,X1,X2,X3)))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 7.49/1.50  
% 7.49/1.50  fof(f75,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f7,conjecture,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f8,negated_conjecture,(
% 7.49/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 7.49/1.50    inference(negated_conjecture,[],[f7])).
% 7.49/1.50  
% 7.49/1.50  fof(f21,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f8])).
% 7.49/1.50  
% 7.49/1.50  fof(f22,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f21])).
% 7.49/1.50  
% 7.49/1.50  fof(f26,plain,(
% 7.49/1.50    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> (! [X3] : (! [X4] : (sP1(X3,X2,X1,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)))),
% 7.49/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 7.49/1.50  
% 7.49/1.50  fof(f25,plain,(
% 7.49/1.50    ! [X3,X2,X1,X0,X4] : (sP1(X3,X2,X1,X0,X4) <=> ! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)))),
% 7.49/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.49/1.50  
% 7.49/1.50  fof(f27,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> sP2(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.49/1.50    inference(definition_folding,[],[f22,f26,f25])).
% 7.49/1.50  
% 7.49/1.50  fof(f50,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : (((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.49/1.50    inference(nnf_transformation,[],[f27])).
% 7.49/1.50  
% 7.49/1.50  fof(f51,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f50])).
% 7.49/1.50  
% 7.49/1.50  fof(f54,plain,(
% 7.49/1.50    ( ! [X0,X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((~sP2(X0,X1,sK10) | ~r3_tsep_1(X0,X1,sK10)) & (sP2(X0,X1,sK10) | r3_tsep_1(X0,X1,sK10)) & m1_pre_topc(sK10,X0) & ~v2_struct_0(sK10))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f53,plain,(
% 7.49/1.50    ( ! [X0] : (? [X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~sP2(X0,sK9,X2) | ~r3_tsep_1(X0,sK9,X2)) & (sP2(X0,sK9,X2) | r3_tsep_1(X0,sK9,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK9,X0) & ~v2_struct_0(sK9))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f52,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : ((~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2)) & (sP2(X0,X1,X2) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~sP2(sK8,X1,X2) | ~r3_tsep_1(sK8,X1,X2)) & (sP2(sK8,X1,X2) | r3_tsep_1(sK8,X1,X2)) & m1_pre_topc(X2,sK8) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK8) & ~v2_struct_0(X1)) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f55,plain,(
% 7.49/1.50    (((~sP2(sK8,sK9,sK10) | ~r3_tsep_1(sK8,sK9,sK10)) & (sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10)) & m1_pre_topc(sK10,sK8) & ~v2_struct_0(sK10)) & m1_pre_topc(sK9,sK8) & ~v2_struct_0(sK9)) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8)),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f51,f54,f53,f52])).
% 7.49/1.50  
% 7.49/1.50  fof(f117,plain,(
% 7.49/1.50    sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f71,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f40,plain,(
% 7.49/1.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (! [X4] : (sP1(X3,X2,X1,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 7.49/1.50    inference(nnf_transformation,[],[f26])).
% 7.49/1.50  
% 7.49/1.50  fof(f41,plain,(
% 7.49/1.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (! [X4] : (sP1(X3,X2,X1,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 7.49/1.50    inference(flattening,[],[f40])).
% 7.49/1.50  
% 7.49/1.50  fof(f42,plain,(
% 7.49/1.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X5] : (! [X6] : (sP1(X5,X2,X1,X0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(X6,X1,X5) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 7.49/1.50    inference(rectify,[],[f41])).
% 7.49/1.50  
% 7.49/1.50  fof(f44,plain,(
% 7.49/1.50    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => (~sP1(X3,X2,X1,X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(sK6(X0,X1,X2),X1,X3) & v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(sK6(X0,X1,X2))))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f43,plain,(
% 7.49/1.50    ! [X2,X1,X0] : (? [X3] : (? [X4] : (~sP1(X3,X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (? [X4] : (~sP1(sK5(X0,X1,X2),X2,X1,X0,X4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) & v5_pre_topc(X4,X1,sK5(X0,X1,X2)) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) & v1_funct_1(X4)) & l1_pre_topc(sK5(X0,X1,X2)) & v2_pre_topc(sK5(X0,X1,X2)) & ~v2_struct_0(sK5(X0,X1,X2))))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f45,plain,(
% 7.49/1.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) & v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2)) & v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) & v1_funct_1(sK6(X0,X1,X2))) & l1_pre_topc(sK5(X0,X1,X2)) & v2_pre_topc(sK5(X0,X1,X2)) & ~v2_struct_0(sK5(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) & ((! [X5] : (! [X6] : (sP1(X5,X2,X1,X0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(X6,X1,X5) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X2)) | ~sP2(X0,X1,X2)))),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f42,f44,f43])).
% 7.49/1.50  
% 7.49/1.50  fof(f92,plain,(
% 7.49/1.50    ( ! [X6,X2,X0,X5,X1] : (sP1(X5,X2,X1,X0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(X6,X1,X5) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~sP2(X0,X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f68,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f69,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f70,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f46,plain,(
% 7.49/1.50    ! [X3,X2,X1,X0,X4] : ((sP1(X3,X2,X1,X0,X4) | ? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~sP1(X3,X2,X1,X0,X4)))),
% 7.49/1.50    inference(nnf_transformation,[],[f25])).
% 7.49/1.50  
% 7.49/1.50  fof(f47,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X5,X1,X0) & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X5))) & (! [X6] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6)) | ~sP1(X0,X1,X2,X3,X4)))),
% 7.49/1.50    inference(rectify,[],[f46])).
% 7.49/1.50  
% 7.49/1.50  fof(f48,plain,(
% 7.49/1.50    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X5,X1,X0) & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)))) & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) & v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7(X0,X1,X2,X3,X4))))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f49,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)))) & m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) & v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7(X0,X1,X2,X3,X4)))) & (! [X6] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6)) | ~sP1(X0,X1,X2,X3,X4)))),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 7.49/1.50  
% 7.49/1.50  fof(f102,plain,(
% 7.49/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X6),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f104,plain,(
% 7.49/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f4,axiom,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f15,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f4])).
% 7.49/1.50  
% 7.49/1.50  fof(f16,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f15])).
% 7.49/1.50  
% 7.49/1.50  fof(f83,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f16])).
% 7.49/1.50  
% 7.49/1.50  fof(f67,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f1,axiom,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f9,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.49/1.50    inference(ennf_transformation,[],[f1])).
% 7.49/1.50  
% 7.49/1.50  fof(f10,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.49/1.50    inference(flattening,[],[f9])).
% 7.49/1.50  
% 7.49/1.50  fof(f28,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.49/1.50    inference(nnf_transformation,[],[f10])).
% 7.49/1.50  
% 7.49/1.50  fof(f56,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f28])).
% 7.49/1.50  
% 7.49/1.50  fof(f66,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f65,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(sK3(X0,X1,X2,X3))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f72,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f101,plain,(
% 7.49/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f73,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f74,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f3,axiom,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2))))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f13,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f3])).
% 7.49/1.50  
% 7.49/1.50  fof(f14,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f13])).
% 7.49/1.50  
% 7.49/1.50  fof(f24,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(definition_folding,[],[f14,f23])).
% 7.49/1.50  
% 7.49/1.50  fof(f33,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | (? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(nnf_transformation,[],[f24])).
% 7.49/1.50  
% 7.49/1.50  fof(f34,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | ? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f33])).
% 7.49/1.50  
% 7.49/1.50  fof(f35,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | ? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X4] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(rectify,[],[f34])).
% 7.49/1.50  
% 7.49/1.50  fof(f36,plain,(
% 7.49/1.50    ! [X2,X1,X0] : (? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (~sP0(sK4(X0,X1,X2),X2,X1,X0) & l1_pre_topc(sK4(X0,X1,X2)) & v2_pre_topc(sK4(X0,X1,X2)) & ~v2_struct_0(sK4(X0,X1,X2))))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f37,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | (~sP0(sK4(X0,X1,X2),X2,X1,X0) & l1_pre_topc(sK4(X0,X1,X2)) & v2_pre_topc(sK4(X0,X1,X2)) & ~v2_struct_0(sK4(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) & ((! [X4] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 7.49/1.50  
% 7.49/1.50  fof(f82,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | ~sP0(sK4(X0,X1,X2),X2,X1,X0) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f37])).
% 7.49/1.50  
% 7.49/1.50  fof(f81,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | l1_pre_topc(sK4(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f37])).
% 7.49/1.50  
% 7.49/1.50  fof(f80,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | v2_pre_topc(sK4(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f37])).
% 7.49/1.50  
% 7.49/1.50  fof(f79,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | ~v2_struct_0(sK4(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f37])).
% 7.49/1.50  
% 7.49/1.50  fof(f91,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~sP2(X0,X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f110,plain,(
% 7.49/1.50    ~v2_struct_0(sK8)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f111,plain,(
% 7.49/1.50    v2_pre_topc(sK8)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f112,plain,(
% 7.49/1.50    l1_pre_topc(sK8)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f113,plain,(
% 7.49/1.50    ~v2_struct_0(sK9)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f114,plain,(
% 7.49/1.50    m1_pre_topc(sK9,sK8)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f115,plain,(
% 7.49/1.50    ~v2_struct_0(sK10)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f116,plain,(
% 7.49/1.50    m1_pre_topc(sK10,sK8)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f99,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f6,axiom,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f19,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f6])).
% 7.49/1.50  
% 7.49/1.50  fof(f20,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f19])).
% 7.49/1.50  
% 7.49/1.50  fof(f38,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | (~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(nnf_transformation,[],[f20])).
% 7.49/1.50  
% 7.49/1.50  fof(f39,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | ~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f90,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f39])).
% 7.49/1.50  
% 7.49/1.50  fof(f5,axiom,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f17,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f5])).
% 7.49/1.50  
% 7.49/1.50  fof(f18,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f17])).
% 7.49/1.50  
% 7.49/1.50  fof(f86,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f18])).
% 7.49/1.50  
% 7.49/1.50  fof(f89,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f39])).
% 7.49/1.50  
% 7.49/1.50  fof(f2,axiom,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f11,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f2])).
% 7.49/1.50  
% 7.49/1.50  fof(f12,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f11])).
% 7.49/1.50  
% 7.49/1.50  fof(f59,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f60,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f109,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f108,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f106,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f105,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | v1_funct_1(sK7(X0,X1,X2,X3,X4))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f58,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f107,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f98,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f97,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f96,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v1_funct_1(sK6(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f95,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | l1_pre_topc(sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f94,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | v2_pre_topc(sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f93,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~v2_struct_0(sK5(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f100,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2)) | ~r1_tsep_1(X1,X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f45])).
% 7.49/1.50  
% 7.49/1.50  fof(f118,plain,(
% 7.49/1.50    ~sP2(sK8,sK9,sK10) | ~r3_tsep_1(sK8,sK9,sK10)),
% 7.49/1.50    inference(cnf_transformation,[],[f55])).
% 7.49/1.50  
% 7.49/1.50  fof(f103,plain,(
% 7.49/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X6),k1_tsep_1(X3,X2,X1),X0) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X6,X1,X0) | ~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X6) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f49])).
% 7.49/1.50  
% 7.49/1.50  fof(f78,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X1] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f37])).
% 7.49/1.50  
% 7.49/1.50  fof(f76,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK3(X0,X1,X2,X3))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f77,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f37])).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11196,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12467,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11196]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_55,negated_conjecture,
% 7.49/1.50      ( sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10) ),
% 7.49/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11157,negated_conjecture,
% 7.49/1.50      ( sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_55]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12506,plain,
% 7.49/1.50      ( sP2(sK8,sK9,sK10) = iProver_top
% 7.49/1.50      | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11157]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_10,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11192,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12471,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11192]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_43,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ sP2(X3,X2,X1)
% 7.49/1.50      | ~ v5_pre_topc(X4,X2,X0)
% 7.49/1.50      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
% 7.49/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | ~ v1_funct_1(X4) ),
% 7.49/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11169,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | ~ sP2(X3_57,X2_57,X1_57)
% 7.49/1.50      | ~ v5_pre_topc(X0_58,X2_57,X0_57)
% 7.49/1.50      | ~ v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57))
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57))))
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | ~ v1_funct_1(X0_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_43]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12494,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | sP2(X3_57,X2_57,X1_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11169]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16032,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57))) = iProver_top
% 7.49/1.50      | sP0(X0_57,X5_57,X2_57,X4_57) = iProver_top
% 7.49/1.50      | sP2(X3_57,X2_57,X1_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57)),X2_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57)),u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12471,c_12494]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_13,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11189,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12474,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11189]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11190,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X2_57),u1_struct_0(X0_57)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12473,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X2_57),u1_struct_0(X0_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11190]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK3(X0,X1,X2,X3)),X2,X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11191,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),X2_57,X0_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12472,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,sK3(X0_57,X1_57,X2_57,X3_57)),X2_57,X0_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11191]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_17825,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X4_57,X0_57,k1_tsep_1(X4_57,X2_57,X5_57),X2_57,sK3(X0_57,X5_57,X2_57,X4_57))) = iProver_top
% 7.49/1.50      | sP0(X0_57,X5_57,X2_57,X4_57) = iProver_top
% 7.49/1.50      | sP2(X3_57,X2_57,X1_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top ),
% 7.49/1.50      inference(forward_subsumption_resolution,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_16032,c_12474,c_12473,c_12472]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_52,plain,
% 7.49/1.50      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X0)
% 7.49/1.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,X5),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.49/1.50      | ~ v1_funct_1(X5) ),
% 7.49/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11160,plain,
% 7.49/1.50      ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | ~ v5_pre_topc(X1_58,X1_57,X0_57)
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
% 7.49/1.50      | ~ v1_funct_1(X1_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_52]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12503,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.50      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11160]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_50,plain,
% 7.49/1.50      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X0)
% 7.49/1.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 7.49/1.50      | ~ v1_funct_1(X5) ),
% 7.49/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11162,plain,
% 7.49/1.50      ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | ~ v5_pre_topc(X1_58,X1_57,X0_57)
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))))
% 7.49/1.50      | ~ v1_funct_1(X1_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_50]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12501,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.50      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) = iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11162]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27,plain,
% 7.49/1.50      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
% 7.49/1.50      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
% 7.49/1.50      | ~ v2_pre_topc(X3)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X3)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X3)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | ~ v1_funct_1(X4) ),
% 7.49/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11178,plain,
% 7.49/1.50      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57),X0_58,k10_tmap_1(X0_57,X3_57,X1_57,X2_57,k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X1_57,X0_58),k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X2_57,X0_58)))
% 7.49/1.50      | ~ v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.50      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))))
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | ~ v2_pre_topc(X3_57)
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | ~ l1_pre_topc(X3_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57)
% 7.49/1.50      | v2_struct_0(X3_57)
% 7.49/1.50      | ~ v1_funct_1(X0_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_27]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12485,plain,
% 7.49/1.50      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57),X0_58,k10_tmap_1(X0_57,X3_57,X1_57,X2_57,k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X1_57,X0_58),k3_tmap_1(X0_57,X3_57,k1_tsep_1(X0_57,X1_57,X2_57),X2_57,X0_58))) = iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11178]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_14,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11188,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | m1_subset_1(sK3(X0_57,X1_57,X2_57,X3_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12475,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | m1_subset_1(sK3(X0_57,X1_57,X2_57,X3_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11188]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1,plain,
% 7.49/1.50      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.49/1.50      | ~ v1_funct_2(X3,X0,X1)
% 7.49/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | ~ v1_funct_1(X2)
% 7.49/1.50      | X2 = X3 ),
% 7.49/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11200,plain,
% 7.49/1.50      ( ~ r2_funct_2(X0_59,X1_59,X0_58,X1_58)
% 7.49/1.50      | ~ v1_funct_2(X1_58,X0_59,X1_59)
% 7.49/1.50      | ~ v1_funct_2(X0_58,X0_59,X1_59)
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 7.49/1.50      | ~ v1_funct_1(X0_58)
% 7.49/1.50      | ~ v1_funct_1(X1_58)
% 7.49/1.50      | X0_58 = X1_58 ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12463,plain,
% 7.49/1.50      ( X0_58 = X1_58
% 7.49/1.50      | r2_funct_2(X0_59,X1_59,X0_58,X1_58) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,X0_59,X1_59) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,X0_59,X1_59) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11200]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_14826,plain,
% 7.49/1.50      ( sK3(X0_57,X1_57,X2_57,X3_57) = X0_58
% 7.49/1.50      | sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | r2_funct_2(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57),sK3(X0_57,X1_57,X2_57,X3_57),X0_58) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12475,c_12463]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_15,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11187,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11245,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11187]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3) | v1_funct_1(sK3(X0,X1,X2,X3)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11186,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11246,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11186]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16973,plain,
% 7.49/1.50      ( v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | sK3(X0_57,X1_57,X2_57,X3_57) = X0_58
% 7.49/1.50      | sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | r2_funct_2(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57),sK3(X0_57,X1_57,X2_57,X3_57),X0_58) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_14826,c_11245,c_11246]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16974,plain,
% 7.49/1.50      ( sK3(X0_57,X1_57,X2_57,X3_57) = X0_58
% 7.49/1.50      | sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | r2_funct_2(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57),sK3(X0_57,X1_57,X2_57,X3_57),X0_58) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_16973]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16985,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK3(X1_57,X3_57,X2_57,X0_57),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK3(X1_57,X3_57,X2_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK3(X1_57,X3_57,X2_57,X0_57)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12485,c_16974]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12477,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(sK3(X0_57,X1_57,X2_57,X3_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11186]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12476,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_2(sK3(X0_57,X1_57,X2_57,X3_57),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11187]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_19902,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)))) != iProver_top ),
% 7.49/1.50      inference(forward_subsumption_resolution,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_16985,c_12477,c_12475,c_12476]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_19906,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),X3_57,X1_57) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),u1_struct_0(X3_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12501,c_19902]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_9,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11193,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12470,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11193]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_53,plain,
% 7.49/1.50      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X0)
% 7.49/1.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.49/1.50      | ~ v1_funct_1(X5)
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,X5)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11159,plain,
% 7.49/1.50      ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | ~ v5_pre_topc(X1_58,X1_57,X0_57)
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
% 7.49/1.50      | ~ v1_funct_1(X1_58)
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_53]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12504,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.50      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11159]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_15347,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.50      | sP0(X0_57,X1_57,X4_57,X5_57) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)),X1_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)))) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12467,c_12504]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11194,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X1_57),u1_struct_0(X0_57)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12469,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),u1_struct_0(X1_57),u1_struct_0(X0_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11194]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3)
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK3(X0,X1,X2,X3)),X1,X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11195,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),X1_57,X0_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12468,plain,
% 7.49/1.50      ( sP0(X0_57,X1_57,X2_57,X3_57) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,sK3(X0_57,X1_57,X2_57,X3_57)),X1_57,X0_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11195]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_17555,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.50      | sP0(X0_57,X1_57,X4_57,X5_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,k3_tmap_1(X5_57,X0_57,k1_tsep_1(X5_57,X4_57,X1_57),X1_57,sK3(X0_57,X1_57,X4_57,X5_57)))) = iProver_top ),
% 7.49/1.50      inference(forward_subsumption_resolution,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_15347,c_12470,c_12469,c_12468]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20012,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))),u1_struct_0(k1_tsep_1(X0_57,X2_57,X3_57)),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top ),
% 7.49/1.50      inference(forward_subsumption_resolution,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_19906,c_12470,c_17555,c_12467,c_12469,c_12468]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20016,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),X3_57,X1_57) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),u1_struct_0(X3_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12503,c_20012]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20254,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP1(X1_57,X3_57,X2_57,X0_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57))) != iProver_top
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top ),
% 7.49/1.50      inference(forward_subsumption_resolution,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_20016,c_12470,c_12467,c_12469,c_12468]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20259,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,X1_57,X2_57,X3_57,k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X2_57,sK3(X1_57,X3_57,X2_57,X0_57)),k3_tmap_1(X0_57,X1_57,k1_tsep_1(X0_57,X2_57,X3_57),X3_57,sK3(X1_57,X3_57,X2_57,X0_57))) = sK3(X1_57,X3_57,X2_57,X0_57)
% 7.49/1.50      | sP0(X1_57,X3_57,X2_57,X0_57) = iProver_top
% 7.49/1.50      | sP2(X0_57,X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_17825,c_20254]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21,plain,
% 7.49/1.50      ( ~ sP0(sK4(X0,X1,X2),X2,X1,X0)
% 7.49/1.50      | r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11184,plain,
% 7.49/1.50      ( ~ sP0(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
% 7.49/1.50      | r3_tsep_1(X0_57,X1_57,X2_57)
% 7.49/1.50      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.50      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12479,plain,
% 7.49/1.50      ( sP0(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57) != iProver_top
% 7.49/1.50      | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11184]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20504,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),X1_57,X2_57,k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X1_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)),k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X2_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57))) = sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
% 7.49/1.50      | sP2(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.50      | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK4(X0_57,X1_57,X2_57)) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK4(X0_57,X1_57,X2_57)) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4(X0_57,X1_57,X2_57)) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_20259,c_12479]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_22,plain,
% 7.49/1.50      ( r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | l1_pre_topc(sK4(X0,X1,X2))
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11183,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57)
% 7.49/1.50      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.50      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | l1_pre_topc(sK4(X0_57,X1_57,X2_57))
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11251,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK4(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11183]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_23,plain,
% 7.49/1.50      ( r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | v2_pre_topc(sK4(X0,X1,X2))
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11182,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57)
% 7.49/1.50      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.50      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | v2_pre_topc(sK4(X0_57,X1_57,X2_57))
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11252,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK4(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11182]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_24,plain,
% 7.49/1.50      ( r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | ~ v2_struct_0(sK4(X0,X1,X2)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11181,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57)
% 7.49/1.50      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.50      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57)
% 7.49/1.50      | ~ v2_struct_0(sK4(X0_57,X1_57,X2_57)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11253,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4(X0_57,X1_57,X2_57)) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11181]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_44,plain,
% 7.49/1.50      ( ~ sP2(X0,X1,X2) | r1_tsep_1(X1,X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11168,plain,
% 7.49/1.50      ( ~ sP2(X0_57,X1_57,X2_57) | r1_tsep_1(X1_57,X2_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_44]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11270,plain,
% 7.49/1.50      ( sP2(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11168]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21008,plain,
% 7.49/1.50      ( v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | k10_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),X1_57,X2_57,k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X1_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)),k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X2_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57))) = sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
% 7.49/1.50      | sP2(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.50      | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_20504,c_11251,c_11252,c_11253,c_11270]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21009,plain,
% 7.49/1.50      ( k10_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),X1_57,X2_57,k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X1_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)),k3_tmap_1(X0_57,sK4(X0_57,X1_57,X2_57),k1_tsep_1(X0_57,X1_57,X2_57),X2_57,sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57))) = sK3(sK4(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57)
% 7.49/1.50      | sP2(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.50      | r3_tsep_1(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_21008]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21022,plain,
% 7.49/1.50      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 7.49/1.50      | r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 7.49/1.50      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.50      | v2_struct_0(sK10) = iProver_top
% 7.49/1.50      | v2_struct_0(sK9) = iProver_top
% 7.49/1.50      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12506,c_21009]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_62,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK8) ),
% 7.49/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_63,plain,
% 7.49/1.50      ( v2_struct_0(sK8) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_61,negated_conjecture,
% 7.49/1.50      ( v2_pre_topc(sK8) ),
% 7.49/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_64,plain,
% 7.49/1.50      ( v2_pre_topc(sK8) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_60,negated_conjecture,
% 7.49/1.50      ( l1_pre_topc(sK8) ),
% 7.49/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_65,plain,
% 7.49/1.50      ( l1_pre_topc(sK8) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_59,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK9) ),
% 7.49/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_66,plain,
% 7.49/1.50      ( v2_struct_0(sK9) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_58,negated_conjecture,
% 7.49/1.50      ( m1_pre_topc(sK9,sK8) ),
% 7.49/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_67,plain,
% 7.49/1.50      ( m1_pre_topc(sK9,sK8) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_57,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK10) ),
% 7.49/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_68,plain,
% 7.49/1.50      ( v2_struct_0(sK10) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_56,negated_conjecture,
% 7.49/1.50      ( m1_pre_topc(sK10,sK8) ),
% 7.49/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_69,plain,
% 7.49/1.50      ( m1_pre_topc(sK10,sK8) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21115,plain,
% 7.49/1.50      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 7.49/1.50      | k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_21022,c_63,c_64,c_65,c_66,c_67,c_68,c_69]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21116,plain,
% 7.49/1.50      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 7.49/1.50      | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_21115]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_36,plain,
% 7.49/1.50      ( sP2(X0,X1,X2)
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11176,plain,
% 7.49/1.50      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.50      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.50      | m1_subset_1(sK6(X0_57,X1_57,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_36]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12487,plain,
% 7.49/1.50      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.50      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6(X0_57,X1_57,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11176]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_32,plain,
% 7.49/1.50      ( r4_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_29,plain,
% 7.49/1.50      ( ~ r4_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ v5_pre_topc(X3,X2,X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X4)
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 7.49/1.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | ~ v1_funct_1(X5) ),
% 7.49/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1026,plain,
% 7.49/1.50      ( ~ r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ v5_pre_topc(X3,X2,X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X4)
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 7.49/1.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 7.49/1.50      | ~ r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | ~ v1_funct_1(X5) ),
% 7.49/1.50      inference(resolution,[status(thm)],[c_32,c_29]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_33,plain,
% 7.49/1.50      ( ~ r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | r1_tsep_1(X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1030,plain,
% 7.49/1.50      ( ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X4)
% 7.49/1.50      | ~ v5_pre_topc(X3,X2,X4)
% 7.49/1.50      | ~ r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | ~ v1_funct_1(X5) ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_1026,c_33,c_32,c_29]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1031,plain,
% 7.49/1.50      ( ~ r3_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ v5_pre_topc(X3,X2,X4)
% 7.49/1.50      | ~ v5_pre_topc(X5,X1,X4)
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X0,X4,X1,X2,X5,X3),k1_tsep_1(X0,X1,X2),X4)
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X4))
% 7.49/1.50      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
% 7.49/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | ~ v1_funct_1(X5) ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_1030]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11146,plain,
% 7.49/1.50      ( ~ r3_tsep_1(X0_57,X1_57,X2_57)
% 7.49/1.50      | ~ v5_pre_topc(X0_58,X2_57,X3_57)
% 7.49/1.50      | ~ v5_pre_topc(X1_58,X1_57,X3_57)
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X0_57,X3_57,X1_57,X2_57,X1_58,X0_58),k1_tsep_1(X0_57,X1_57,X2_57),X3_57)
% 7.49/1.50      | ~ v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X3_57))
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X3_57))
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.50      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X3_57))))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X3_57))))
% 7.49/1.50      | ~ v2_pre_topc(X0_57)
% 7.49/1.50      | ~ v2_pre_topc(X3_57)
% 7.49/1.50      | ~ l1_pre_topc(X0_57)
% 7.49/1.50      | ~ l1_pre_topc(X3_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57)
% 7.49/1.50      | v2_struct_0(X3_57)
% 7.49/1.50      | ~ v1_funct_1(X0_58)
% 7.49/1.50      | ~ v1_funct_1(X1_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_1031]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12517,plain,
% 7.49/1.50      ( r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_58,X2_57,X3_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(X1_58,X1_57,X3_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X0_57,X3_57,X1_57,X2_57,X1_58,X0_58),k1_tsep_1(X0_57,X1_57,X2_57),X3_57) = iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X3_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X3_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X3_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X3_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11146]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X1,X5)
% 7.49/1.50      | ~ m1_pre_topc(X4,X5)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X5)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X5)
% 7.49/1.50      | v2_struct_0(X5)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11198,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57))
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X3_57)
% 7.49/1.50      | ~ m1_pre_topc(X0_57,X3_57)
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
% 7.49/1.50      | ~ v2_pre_topc(X3_57)
% 7.49/1.50      | ~ v2_pre_topc(X1_57)
% 7.49/1.50      | ~ l1_pre_topc(X3_57)
% 7.49/1.50      | ~ l1_pre_topc(X1_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57)
% 7.49/1.50      | v2_struct_0(X3_57)
% 7.49/1.50      | ~ v1_funct_1(X0_58)
% 7.49/1.50      | ~ v1_funct_1(X1_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12465,plain,
% 7.49/1.50      ( v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57)) = iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11198]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X1,X5)
% 7.49/1.50      | ~ m1_pre_topc(X4,X5)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X5)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X5)
% 7.49/1.50      | v2_struct_0(X5)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11199,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57))
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X3_57)
% 7.49/1.50      | ~ m1_pre_topc(X0_57,X3_57)
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57))))
% 7.49/1.50      | ~ v2_pre_topc(X3_57)
% 7.49/1.50      | ~ v2_pre_topc(X1_57)
% 7.49/1.50      | ~ l1_pre_topc(X3_57)
% 7.49/1.50      | ~ l1_pre_topc(X1_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57)
% 7.49/1.50      | v2_struct_0(X3_57)
% 7.49/1.50      | ~ v1_funct_1(X0_58)
% 7.49/1.50      | ~ v1_funct_1(X1_58) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12464,plain,
% 7.49/1.50      ( v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X0_57)),u1_struct_0(X1_57)))) = iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11199]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_45,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_tsep_1(X3,X2,X1),X0)
% 7.49/1.50      | ~ v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 7.49/1.50      | ~ m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 7.49/1.50      | ~ v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X4,sK7(X0,X1,X2,X3,X4))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11167,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | ~ v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57)
% 7.49/1.50      | ~ v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))
% 7.49/1.50      | ~ m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57))))
% 7.49/1.50      | ~ v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_45]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12496,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11167]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_14011,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12464,c_12496]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_46,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | m1_subset_1(sK7(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11166,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_46]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11274,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11166]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_48,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | v1_funct_2(sK7(X0,X1,X2,X3,X4),u1_struct_0(X1),u1_struct_0(X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11164,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_48]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11280,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11164]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_49,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4) | v1_funct_1(sK7(X0,X1,X2,X3,X4)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11163,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_49]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11283,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11163]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18796,plain,
% 7.49/1.50      ( v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_14011,c_11274,c_11280,c_11283]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18797,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_18796]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12497,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11166]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X1,X5)
% 7.49/1.50      | ~ m1_pre_topc(X4,X5)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X5)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X5)
% 7.49/1.50      | v2_struct_0(X5)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11197,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 7.49/1.50      | ~ v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57))
% 7.49/1.50      | ~ m1_pre_topc(X2_57,X3_57)
% 7.49/1.50      | ~ m1_pre_topc(X0_57,X3_57)
% 7.49/1.50      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 7.49/1.50      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
% 7.49/1.50      | ~ v2_pre_topc(X3_57)
% 7.49/1.50      | ~ v2_pre_topc(X1_57)
% 7.49/1.50      | ~ l1_pre_topc(X3_57)
% 7.49/1.50      | ~ l1_pre_topc(X1_57)
% 7.49/1.50      | v2_struct_0(X0_57)
% 7.49/1.50      | v2_struct_0(X1_57)
% 7.49/1.50      | v2_struct_0(X2_57)
% 7.49/1.50      | v2_struct_0(X3_57)
% 7.49/1.50      | ~ v1_funct_1(X0_58)
% 7.49/1.50      | ~ v1_funct_1(X1_58)
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12466,plain,
% 7.49/1.50      ( v1_funct_2(X0_58,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_57,X1_57,X2_57,X0_57,X1_58,X0_58)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11197]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_14738,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X4_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X5_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X4_57,X5_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X5_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X5_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X4_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X5_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X5_57,X0_57,X4_57,X1_57,X1_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12497,c_12466]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18124,plain,
% 7.49/1.50      ( v1_funct_1(k10_tmap_1(X5_57,X0_57,X4_57,X1_57,X1_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) = iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.50      | v2_struct_0(X5_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X4_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | l1_pre_topc(X5_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X5_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | m1_pre_topc(X4_57,X5_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X5_57) != iProver_top
% 7.49/1.50      | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X4_57),u1_struct_0(X0_57)) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_14738,c_11280,c_11283]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18125,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v1_funct_2(X1_58,u1_struct_0(X4_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X5_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X4_57,X5_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X5_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X5_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X4_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X5_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X5_57,X0_57,X4_57,X1_57,X1_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58))) = iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_18124]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18819,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top ),
% 7.49/1.50      inference(forward_subsumption_resolution,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_18797,c_18125]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18824,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12465,c_18819]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18865,plain,
% 7.49/1.50      ( v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_18824,c_11274,c_11280,c_11283]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18866,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,sK7(X0_57,X1_57,X2_57,X3_57,X0_58)),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_18865]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18886,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | r3_tsep_1(X3_57,X2_57,X1_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),X1_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7(X0_57,X1_57,X2_57,X3_57,X0_58)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12517,c_18866]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_47,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4) | v5_pre_topc(sK7(X0,X1,X2,X3,X4),X1,X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11165,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.50      | v5_pre_topc(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),X1_57,X0_57) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_47]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11277,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | v5_pre_topc(sK7(X0_57,X1_57,X2_57,X3_57,X0_58),X1_57,X0_57) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_11165]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_19000,plain,
% 7.49/1.50      ( v1_funct_1(X0_58) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.50      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | r3_tsep_1(X3_57,X2_57,X1_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_18886,c_11274,c_11277,c_11280,c_11283]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_19001,plain,
% 7.49/1.50      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) = iProver_top
% 7.49/1.50      | r3_tsep_1(X3_57,X2_57,X1_57) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_58,X2_57,X0_57) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_58,u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_57,X3_57) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 7.49/1.51      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X3_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X3_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X2_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.51      | v1_funct_1(X0_58) != iProver_top ),
% 7.49/1.51      inference(renaming,[status(thm)],[c_19000]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_19024,plain,
% 7.49/1.51      ( sP1(sK5(X0_57,X1_57,X2_57),X3_57,X1_57,X4_57,sK6(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.51      | sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r3_tsep_1(X4_57,X1_57,X3_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(sK6(X0_57,X1_57,X2_57),X1_57,sK5(X0_57,X1_57,X2_57)) != iProver_top
% 7.49/1.51      | v1_funct_2(sK6(X0_57,X1_57,X2_57),u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))) != iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X3_57,X4_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X4_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X4_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK5(X0_57,X1_57,X2_57)) != iProver_top
% 7.49/1.51      | l1_pre_topc(X4_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK5(X0_57,X1_57,X2_57)) != iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X4_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X3_57) = iProver_top
% 7.49/1.51      | v2_struct_0(sK5(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.51      | v1_funct_1(sK6(X0_57,X1_57,X2_57)) != iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_12487,c_19001]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_37,plain,
% 7.49/1.51      ( sP2(X0,X1,X2)
% 7.49/1.51      | v5_pre_topc(sK6(X0,X1,X2),X1,sK5(X0,X1,X2))
% 7.49/1.51      | ~ r1_tsep_1(X1,X2) ),
% 7.49/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11175,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | v5_pre_topc(sK6(X0_57,X1_57,X2_57),X1_57,sK5(X0_57,X1_57,X2_57))
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_37]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11261,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | v5_pre_topc(sK6(X0_57,X1_57,X2_57),X1_57,sK5(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11175]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_38,plain,
% 7.49/1.51      ( sP2(X0,X1,X2)
% 7.49/1.51      | v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
% 7.49/1.51      | ~ r1_tsep_1(X1,X2) ),
% 7.49/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11174,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | v1_funct_2(sK6(X0_57,X1_57,X2_57),u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57)))
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_38]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11262,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | v1_funct_2(sK6(X0_57,X1_57,X2_57),u1_struct_0(X1_57),u1_struct_0(sK5(X0_57,X1_57,X2_57))) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11174]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_39,plain,
% 7.49/1.51      ( sP2(X0,X1,X2) | ~ r1_tsep_1(X1,X2) | v1_funct_1(sK6(X0,X1,X2)) ),
% 7.49/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11173,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.51      | v1_funct_1(sK6(X0_57,X1_57,X2_57)) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_39]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11263,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | v1_funct_1(sK6(X0_57,X1_57,X2_57)) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11173]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_40,plain,
% 7.49/1.51      ( sP2(X0,X1,X2) | ~ r1_tsep_1(X1,X2) | l1_pre_topc(sK5(X0,X1,X2)) ),
% 7.49/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11172,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.51      | l1_pre_topc(sK5(X0_57,X1_57,X2_57)) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_40]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11264,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK5(X0_57,X1_57,X2_57)) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11172]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_41,plain,
% 7.49/1.51      ( sP2(X0,X1,X2) | ~ r1_tsep_1(X1,X2) | v2_pre_topc(sK5(X0,X1,X2)) ),
% 7.49/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11171,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.51      | v2_pre_topc(sK5(X0_57,X1_57,X2_57)) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_41]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11265,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK5(X0_57,X1_57,X2_57)) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11171]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_42,plain,
% 7.49/1.51      ( sP2(X0,X1,X2)
% 7.49/1.51      | ~ r1_tsep_1(X1,X2)
% 7.49/1.51      | ~ v2_struct_0(sK5(X0,X1,X2)) ),
% 7.49/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11170,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57)
% 7.49/1.51      | ~ v2_struct_0(sK5(X0_57,X1_57,X2_57)) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_42]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11266,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | v2_struct_0(sK5(X0_57,X1_57,X2_57)) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11170]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_19374,plain,
% 7.49/1.51      ( l1_pre_topc(X4_57) != iProver_top
% 7.49/1.51      | sP1(sK5(X0_57,X1_57,X2_57),X3_57,X1_57,X4_57,sK6(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.51      | sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r3_tsep_1(X4_57,X1_57,X3_57) != iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X3_57,X4_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X4_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X4_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X4_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X3_57) = iProver_top ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_19024,c_11261,c_11262,c_11263,c_11264,c_11265,c_11266]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_19375,plain,
% 7.49/1.51      ( sP1(sK5(X0_57,X1_57,X2_57),X3_57,X1_57,X4_57,sK6(X0_57,X1_57,X2_57)) = iProver_top
% 7.49/1.51      | sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r3_tsep_1(X4_57,X1_57,X3_57) != iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X3_57,X4_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X4_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X4_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X4_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X4_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X3_57) = iProver_top ),
% 7.49/1.51      inference(renaming,[status(thm)],[c_19374]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_35,plain,
% 7.49/1.51      ( ~ sP1(sK5(X0,X1,X2),X2,X1,X0,sK6(X0,X1,X2))
% 7.49/1.51      | sP2(X0,X1,X2)
% 7.49/1.51      | ~ r1_tsep_1(X1,X2) ),
% 7.49/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11177,plain,
% 7.49/1.51      ( ~ sP1(sK5(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57,sK6(X0_57,X1_57,X2_57))
% 7.49/1.51      | sP2(X0_57,X1_57,X2_57)
% 7.49/1.51      | ~ r1_tsep_1(X1_57,X2_57) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_35]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_12486,plain,
% 7.49/1.51      ( sP1(sK5(X0_57,X1_57,X2_57),X2_57,X1_57,X0_57,sK6(X0_57,X1_57,X2_57)) != iProver_top
% 7.49/1.51      | sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11177]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_19391,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_19375,c_12486]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11179,plain,
% 7.49/1.51      ( ~ r3_tsep_1(X0_57,X1_57,X2_57)
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57)
% 7.49/1.51      | ~ m1_pre_topc(X2_57,X0_57)
% 7.49/1.51      | ~ m1_pre_topc(X1_57,X0_57)
% 7.49/1.51      | ~ v2_pre_topc(X0_57)
% 7.49/1.51      | ~ l1_pre_topc(X0_57)
% 7.49/1.51      | v2_struct_0(X0_57)
% 7.49/1.51      | v2_struct_0(X1_57)
% 7.49/1.51      | v2_struct_0(X2_57) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_33]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11255,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.51      | r1_tsep_1(X1_57,X2_57) = iProver_top
% 7.49/1.51      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11179]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_19396,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.51      | sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_19391,c_11255]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_19397,plain,
% 7.49/1.51      ( sP2(X0_57,X1_57,X2_57) = iProver_top
% 7.49/1.51      | r3_tsep_1(X0_57,X1_57,X2_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X1_57) = iProver_top
% 7.49/1.51      | v2_struct_0(X2_57) = iProver_top ),
% 7.49/1.51      inference(renaming,[status(thm)],[c_19396]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_21121,plain,
% 7.49/1.51      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)
% 7.49/1.51      | sP2(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_21116,c_19397]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_54,negated_conjecture,
% 7.49/1.51      ( ~ sP2(sK8,sK9,sK10) | ~ r3_tsep_1(sK8,sK9,sK10) ),
% 7.49/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_71,plain,
% 7.49/1.51      ( sP2(sK8,sK9,sK10) != iProver_top
% 7.49/1.51      | r3_tsep_1(sK8,sK9,sK10) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_21148,plain,
% 7.49/1.51      ( k10_tmap_1(sK8,sK4(sK8,sK9,sK10),sK9,sK10,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8) ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_21121,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_71,c_21116]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_16028,plain,
% 7.49/1.51      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | sP1(X0_57,X4_57,k1_tsep_1(X3_57,X2_57,X1_57),X5_57,k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top
% 7.49/1.51      | sP2(X5_57,k1_tsep_1(X3_57,X2_57,X1_57),X4_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) != iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.51      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) != iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_12501,c_12494]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_51,plain,
% 7.49/1.51      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.49/1.51      | ~ v5_pre_topc(X5,X1,X0)
% 7.49/1.51      | v5_pre_topc(k10_tmap_1(X3,X0,X2,X1,X4,X5),k1_tsep_1(X3,X2,X1),X0)
% 7.49/1.51      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
% 7.49/1.51      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.49/1.51      | ~ v1_funct_1(X5) ),
% 7.49/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11161,plain,
% 7.49/1.51      ( ~ sP1(X0_57,X1_57,X2_57,X3_57,X0_58)
% 7.49/1.51      | ~ v5_pre_topc(X1_58,X1_57,X0_57)
% 7.49/1.51      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57)
% 7.49/1.51      | ~ v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57))
% 7.49/1.51      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
% 7.49/1.51      | ~ v1_funct_1(X1_58) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_51]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11289,plain,
% 7.49/1.51      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) = iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11161]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11292,plain,
% 7.49/1.51      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | v1_funct_2(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),u1_struct_0(k1_tsep_1(X3_57,X2_57,X1_57)),u1_struct_0(X0_57)) = iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11160]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11295,plain,
% 7.49/1.51      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v1_funct_1(X1_58) != iProver_top
% 7.49/1.51      | v1_funct_1(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11159]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_18146,plain,
% 7.49/1.51      ( v1_funct_1(X1_58) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | sP2(X5_57,k1_tsep_1(X3_57,X2_57,X1_57),X4_57) != iProver_top
% 7.49/1.51      | sP1(X0_57,X4_57,k1_tsep_1(X3_57,X2_57,X1_57),X5_57,k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top
% 7.49/1.51      | sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_16028,c_11289,c_11292,c_11295]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_18147,plain,
% 7.49/1.51      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | sP1(X0_57,X4_57,k1_tsep_1(X3_57,X2_57,X1_57),X5_57,k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58)) = iProver_top
% 7.49/1.51      | sP2(X5_57,k1_tsep_1(X3_57,X2_57,X1_57),X4_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.51      inference(renaming,[status(thm)],[c_18146]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_21154,plain,
% 7.49/1.51      ( sP1(sK4(sK8,sK9,sK10),X0_57,k1_tsep_1(sK8,sK9,sK10),X1_57,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)) = iProver_top
% 7.49/1.51      | sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
% 7.49/1.51      | sP2(X1_57,k1_tsep_1(sK8,sK9,sK10),X0_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
% 7.49/1.51      | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_21148,c_18147]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22519,plain,
% 7.49/1.51      ( sP1(sK4(sK8,sK9,sK10),X0_57,k1_tsep_1(sK8,sK9,sK10),X1_57,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)) = iProver_top
% 7.49/1.51      | sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
% 7.49/1.51      | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | sP2(X1_57,k1_tsep_1(sK8,sK9,sK10),X0_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_12467,c_21154]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_70,plain,
% 7.49/1.51      ( sP2(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_25,plain,
% 7.49/1.51      ( sP0(X0,X1,X2,X3)
% 7.49/1.51      | ~ r3_tsep_1(X3,X2,X1)
% 7.49/1.51      | ~ m1_pre_topc(X1,X3)
% 7.49/1.51      | ~ m1_pre_topc(X2,X3)
% 7.49/1.51      | ~ v2_pre_topc(X3)
% 7.49/1.51      | ~ v2_pre_topc(X0)
% 7.49/1.51      | ~ l1_pre_topc(X3)
% 7.49/1.51      | ~ l1_pre_topc(X0)
% 7.49/1.51      | v2_struct_0(X3)
% 7.49/1.51      | v2_struct_0(X2)
% 7.49/1.51      | v2_struct_0(X1)
% 7.49/1.51      | v2_struct_0(X0) ),
% 7.49/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11180,plain,
% 7.49/1.51      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.51      | ~ r3_tsep_1(X3_57,X2_57,X1_57)
% 7.49/1.51      | ~ m1_pre_topc(X1_57,X3_57)
% 7.49/1.51      | ~ m1_pre_topc(X2_57,X3_57)
% 7.49/1.51      | ~ v2_pre_topc(X0_57)
% 7.49/1.51      | ~ v2_pre_topc(X3_57)
% 7.49/1.51      | ~ l1_pre_topc(X0_57)
% 7.49/1.51      | ~ l1_pre_topc(X3_57)
% 7.49/1.51      | v2_struct_0(X0_57)
% 7.49/1.51      | v2_struct_0(X1_57)
% 7.49/1.51      | v2_struct_0(X2_57)
% 7.49/1.51      | v2_struct_0(X3_57) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_25]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13503,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
% 7.49/1.51      | ~ r3_tsep_1(X0_57,sK9,sK10)
% 7.49/1.51      | ~ m1_pre_topc(sK10,X0_57)
% 7.49/1.51      | ~ m1_pre_topc(sK9,X0_57)
% 7.49/1.51      | ~ v2_pre_topc(X0_57)
% 7.49/1.51      | ~ v2_pre_topc(sK4(X0_57,sK9,sK10))
% 7.49/1.51      | ~ l1_pre_topc(X0_57)
% 7.49/1.51      | ~ l1_pre_topc(sK4(X0_57,sK9,sK10))
% 7.49/1.51      | v2_struct_0(X0_57)
% 7.49/1.51      | v2_struct_0(sK4(X0_57,sK9,sK10))
% 7.49/1.51      | v2_struct_0(sK10)
% 7.49/1.51      | v2_struct_0(sK9) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11180]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13504,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
% 7.49/1.51      | r3_tsep_1(X0_57,sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(X0_57,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(X0_57,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(sK4(X0_57,sK9,sK10)) = iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13503]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13506,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | r3_tsep_1(sK8,sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13504]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_12502,plain,
% 7.49/1.51      ( sP1(X0_57,X1_57,X2_57,X3_57,X0_58) != iProver_top
% 7.49/1.51      | v5_pre_topc(X1_58,X1_57,X0_57) != iProver_top
% 7.49/1.51      | v5_pre_topc(k10_tmap_1(X3_57,X0_57,X2_57,X1_57,X0_58,X1_58),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) = iProver_top
% 7.49/1.51      | v1_funct_2(X1_58,u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
% 7.49/1.51      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 7.49/1.51      | v1_funct_1(X1_58) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_11161]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_21159,plain,
% 7.49/1.51      ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
% 7.49/1.51      | m1_subset_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))))) != iProver_top
% 7.49/1.51      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_21148,c_12502]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_21920,plain,
% 7.49/1.51      ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
% 7.49/1.51      | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) != iProver_top
% 7.49/1.51      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_12467,c_21159]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_5,plain,
% 7.49/1.51      ( sP0(X0,X1,X2,X3)
% 7.49/1.51      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
% 7.49/1.51      | ~ v1_funct_2(sK3(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 7.49/1.51      | ~ m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 7.49/1.51      | ~ v1_funct_1(sK3(X0,X1,X2,X3)) ),
% 7.49/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_399,plain,
% 7.49/1.51      ( ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
% 7.49/1.51      | sP0(X0,X1,X2,X3) ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_5,c_16,c_15,c_14]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_400,plain,
% 7.49/1.51      ( sP0(X0,X1,X2,X3)
% 7.49/1.51      | ~ v5_pre_topc(sK3(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
% 7.49/1.51      inference(renaming,[status(thm)],[c_399]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_11149,plain,
% 7.49/1.51      ( sP0(X0_57,X1_57,X2_57,X3_57)
% 7.49/1.51      | ~ v5_pre_topc(sK3(X0_57,X1_57,X2_57,X3_57),k1_tsep_1(X3_57,X2_57,X1_57),X0_57) ),
% 7.49/1.51      inference(subtyping,[status(esa)],[c_400]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13501,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
% 7.49/1.51      | ~ v5_pre_topc(sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57),k1_tsep_1(X0_57,sK9,sK10),sK4(X0_57,sK9,sK10)) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11149]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13512,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
% 7.49/1.51      | v5_pre_topc(sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57),k1_tsep_1(X0_57,sK9,sK10),sK4(X0_57,sK9,sK10)) != iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13501]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13514,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | v5_pre_topc(sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8),k1_tsep_1(sK8,sK9,sK10),sK4(sK8,sK9,sK10)) != iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13512]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13497,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
% 7.49/1.51      | v1_funct_1(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57))) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11193]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13528,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
% 7.49/1.51      | v1_funct_1(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57))) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13497]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13530,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | v1_funct_1(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13528]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13493,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
% 7.49/1.51      | v1_funct_2(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),u1_struct_0(sK10),u1_struct_0(sK4(X0_57,sK9,sK10))) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11194]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13544,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
% 7.49/1.51      | v1_funct_2(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),u1_struct_0(sK10),u1_struct_0(sK4(X0_57,sK9,sK10))) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13493]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13546,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | v1_funct_2(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),u1_struct_0(sK10),u1_struct_0(sK4(sK8,sK9,sK10))) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13544]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13492,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),sK10,sK4(X0_57,sK9,sK10)) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11195]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13548,plain,
% 7.49/1.51      ( sP0(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57) = iProver_top
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(X0_57,sK4(X0_57,sK9,sK10),k1_tsep_1(X0_57,sK9,sK10),sK10,sK3(sK4(X0_57,sK9,sK10),sK10,sK9,X0_57)),sK10,sK4(X0_57,sK9,sK10)) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13492]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13550,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | v5_pre_topc(k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK10,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8)),sK10,sK4(sK8,sK9,sK10)) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13548]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22733,plain,
% 7.49/1.51      ( sP1(sK4(sK8,sK9,sK10),sK10,sK9,sK8,k3_tmap_1(sK8,sK4(sK8,sK9,sK10),k1_tsep_1(sK8,sK9,sK10),sK9,sK3(sK4(sK8,sK9,sK10),sK10,sK9,sK8))) != iProver_top
% 7.49/1.51      | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_21920,c_13514,c_13530,c_13546,c_13550]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22740,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | sP2(sK8,sK9,sK10) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_17825,c_22733]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22770,plain,
% 7.49/1.51      ( v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_22519,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_13506,
% 7.49/1.51                 c_22740]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22771,plain,
% 7.49/1.51      ( sP0(sK4(sK8,sK9,sK10),sK10,sK9,sK8) = iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top ),
% 7.49/1.51      inference(renaming,[status(thm)],[c_22770]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22778,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_22771,c_12479]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_26,plain,
% 7.49/1.51      ( ~ r3_tsep_1(X0,X1,X2)
% 7.49/1.51      | r1_tsep_1(X1,X2)
% 7.49/1.51      | ~ m1_pre_topc(X2,X0)
% 7.49/1.51      | ~ m1_pre_topc(X1,X0)
% 7.49/1.51      | ~ v2_pre_topc(X0)
% 7.49/1.51      | ~ l1_pre_topc(X0)
% 7.49/1.51      | v2_struct_0(X0)
% 7.49/1.51      | v2_struct_0(X1)
% 7.49/1.51      | v2_struct_0(X2) ),
% 7.49/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_490,plain,
% 7.49/1.51      ( sP2(sK8,sK9,sK10) | r3_tsep_1(sK8,sK9,sK10) ),
% 7.49/1.51      inference(prop_impl,[status(thm)],[c_55]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_5916,plain,
% 7.49/1.51      ( sP2(sK8,sK9,sK10)
% 7.49/1.51      | r1_tsep_1(X0,X1)
% 7.49/1.51      | ~ m1_pre_topc(X1,X2)
% 7.49/1.51      | ~ m1_pre_topc(X0,X2)
% 7.49/1.51      | ~ v2_pre_topc(X2)
% 7.49/1.51      | ~ l1_pre_topc(X2)
% 7.49/1.51      | v2_struct_0(X2)
% 7.49/1.51      | v2_struct_0(X0)
% 7.49/1.51      | v2_struct_0(X1)
% 7.49/1.51      | sK10 != X1
% 7.49/1.51      | sK9 != X0
% 7.49/1.51      | sK8 != X2 ),
% 7.49/1.51      inference(resolution_lifted,[status(thm)],[c_26,c_490]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_5917,plain,
% 7.49/1.51      ( sP2(sK8,sK9,sK10)
% 7.49/1.51      | r1_tsep_1(sK9,sK10)
% 7.49/1.51      | ~ m1_pre_topc(sK10,sK8)
% 7.49/1.51      | ~ m1_pre_topc(sK9,sK8)
% 7.49/1.51      | ~ v2_pre_topc(sK8)
% 7.49/1.51      | ~ l1_pre_topc(sK8)
% 7.49/1.51      | v2_struct_0(sK10)
% 7.49/1.51      | v2_struct_0(sK9)
% 7.49/1.51      | v2_struct_0(sK8) ),
% 7.49/1.51      inference(unflattening,[status(thm)],[c_5916]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_1573,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10)
% 7.49/1.51      | r1_tsep_1(X0,X1)
% 7.49/1.51      | sK10 != X1
% 7.49/1.51      | sK9 != X0
% 7.49/1.51      | sK8 != X2 ),
% 7.49/1.51      inference(resolution_lifted,[status(thm)],[c_44,c_490]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_1574,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10) | r1_tsep_1(sK9,sK10) ),
% 7.49/1.51      inference(unflattening,[status(thm)],[c_1573]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_5919,plain,
% 7.49/1.51      ( r1_tsep_1(sK9,sK10) ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_5917,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_54,c_1574]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_5921,plain,
% 7.49/1.51      ( r1_tsep_1(sK9,sK10) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_5919]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13259,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,sK9,sK10)
% 7.49/1.51      | ~ r1_tsep_1(sK9,sK10)
% 7.49/1.51      | ~ m1_pre_topc(sK10,X0_57)
% 7.49/1.51      | ~ m1_pre_topc(sK9,X0_57)
% 7.49/1.51      | ~ v2_pre_topc(X0_57)
% 7.49/1.51      | ~ l1_pre_topc(X0_57)
% 7.49/1.51      | v2_struct_0(X0_57)
% 7.49/1.51      | ~ v2_struct_0(sK4(X0_57,sK9,sK10))
% 7.49/1.51      | v2_struct_0(sK10)
% 7.49/1.51      | v2_struct_0(sK9) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11181]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13300,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(sK4(X0_57,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13259]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13302,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK4(sK8,sK9,sK10)) != iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13300]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13258,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,sK9,sK10)
% 7.49/1.51      | ~ r1_tsep_1(sK9,sK10)
% 7.49/1.51      | ~ m1_pre_topc(sK10,X0_57)
% 7.49/1.51      | ~ m1_pre_topc(sK9,X0_57)
% 7.49/1.51      | ~ v2_pre_topc(X0_57)
% 7.49/1.51      | v2_pre_topc(sK4(X0_57,sK9,sK10))
% 7.49/1.51      | ~ l1_pre_topc(X0_57)
% 7.49/1.51      | v2_struct_0(X0_57)
% 7.49/1.51      | v2_struct_0(sK10)
% 7.49/1.51      | v2_struct_0(sK9) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11182]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13304,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(X0_57,sK9,sK10)) = iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13258]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13306,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13304]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13257,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,sK9,sK10)
% 7.49/1.51      | ~ r1_tsep_1(sK9,sK10)
% 7.49/1.51      | ~ m1_pre_topc(sK10,X0_57)
% 7.49/1.51      | ~ m1_pre_topc(sK9,X0_57)
% 7.49/1.51      | ~ v2_pre_topc(X0_57)
% 7.49/1.51      | ~ l1_pre_topc(X0_57)
% 7.49/1.51      | l1_pre_topc(sK4(X0_57,sK9,sK10))
% 7.49/1.51      | v2_struct_0(X0_57)
% 7.49/1.51      | v2_struct_0(sK10)
% 7.49/1.51      | v2_struct_0(sK9) ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_11183]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13308,plain,
% 7.49/1.51      ( r3_tsep_1(X0_57,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,X0_57) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,X0_57) != iProver_top
% 7.49/1.51      | v2_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(X0_57) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(X0_57,sK9,sK10)) = iProver_top
% 7.49/1.51      | v2_struct_0(X0_57) = iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top ),
% 7.49/1.51      inference(predicate_to_equality,[status(thm)],[c_13257]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_13310,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | r1_tsep_1(sK9,sK10) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK4(sK8,sK9,sK10)) = iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(instantiation,[status(thm)],[c_13308]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22948,plain,
% 7.49/1.51      ( r3_tsep_1(sK8,sK9,sK10) = iProver_top ),
% 7.49/1.51      inference(global_propositional_subsumption,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_22778,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_5921,
% 7.49/1.51                 c_13302,c_13306,c_13310]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(c_22953,plain,
% 7.49/1.51      ( sP2(sK8,sK9,sK10) = iProver_top
% 7.49/1.51      | m1_pre_topc(sK10,sK8) != iProver_top
% 7.49/1.51      | m1_pre_topc(sK9,sK8) != iProver_top
% 7.49/1.51      | v2_pre_topc(sK8) != iProver_top
% 7.49/1.51      | l1_pre_topc(sK8) != iProver_top
% 7.49/1.51      | v2_struct_0(sK10) = iProver_top
% 7.49/1.51      | v2_struct_0(sK9) = iProver_top
% 7.49/1.51      | v2_struct_0(sK8) = iProver_top ),
% 7.49/1.51      inference(superposition,[status(thm)],[c_22948,c_19397]) ).
% 7.49/1.51  
% 7.49/1.51  cnf(contradiction,plain,
% 7.49/1.51      ( $false ),
% 7.49/1.51      inference(minisat,
% 7.49/1.51                [status(thm)],
% 7.49/1.51                [c_22953,c_22948,c_71,c_69,c_68,c_67,c_66,c_65,c_64,c_63]) ).
% 7.49/1.51  
% 7.49/1.51  
% 7.49/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.51  
% 7.49/1.51  ------                               Statistics
% 7.49/1.51  
% 7.49/1.51  ------ General
% 7.49/1.51  
% 7.49/1.51  abstr_ref_over_cycles:                  0
% 7.49/1.51  abstr_ref_under_cycles:                 0
% 7.49/1.51  gc_basic_clause_elim:                   0
% 7.49/1.51  forced_gc_time:                         0
% 7.49/1.51  parsing_time:                           0.01
% 7.49/1.51  unif_index_cands_time:                  0.
% 7.49/1.51  unif_index_add_time:                    0.
% 7.49/1.51  orderings_time:                         0.
% 7.49/1.51  out_proof_time:                         0.03
% 7.49/1.51  total_time:                             0.895
% 7.49/1.51  num_of_symbols:                         62
% 7.49/1.51  num_of_terms:                           19638
% 7.49/1.51  
% 7.49/1.51  ------ Preprocessing
% 7.49/1.51  
% 7.49/1.51  num_of_splits:                          0
% 7.49/1.51  num_of_split_atoms:                     0
% 7.49/1.51  num_of_reused_defs:                     0
% 7.49/1.51  num_eq_ax_congr_red:                    139
% 7.49/1.51  num_of_sem_filtered_clauses:            1
% 7.49/1.51  num_of_subtypes:                        5
% 7.49/1.51  monotx_restored_types:                  0
% 7.49/1.51  sat_num_of_epr_types:                   0
% 7.49/1.51  sat_num_of_non_cyclic_types:            0
% 7.49/1.51  sat_guarded_non_collapsed_types:        1
% 7.49/1.51  num_pure_diseq_elim:                    0
% 7.49/1.51  simp_replaced_by:                       0
% 7.49/1.51  res_preprocessed:                       251
% 7.49/1.51  prep_upred:                             0
% 7.49/1.51  prep_unflattend:                        372
% 7.49/1.51  smt_new_axioms:                         0
% 7.49/1.51  pred_elim_cands:                        14
% 7.49/1.51  pred_elim:                              1
% 7.49/1.51  pred_elim_cl:                           2
% 7.49/1.51  pred_elim_cycles:                       13
% 7.49/1.51  merged_defs:                            8
% 7.49/1.51  merged_defs_ncl:                        0
% 7.49/1.51  bin_hyper_res:                          8
% 7.49/1.51  prep_cycles:                            4
% 7.49/1.51  pred_elim_time:                         0.186
% 7.49/1.51  splitting_time:                         0.
% 7.49/1.51  sem_filter_time:                        0.
% 7.49/1.51  monotx_time:                            0.
% 7.49/1.51  subtype_inf_time:                       0.002
% 7.49/1.51  
% 7.49/1.51  ------ Problem properties
% 7.49/1.51  
% 7.49/1.51  clauses:                                57
% 7.49/1.51  conjectures:                            9
% 7.49/1.51  epr:                                    12
% 7.49/1.51  horn:                                   20
% 7.49/1.51  ground:                                 9
% 7.49/1.51  unary:                                  7
% 7.49/1.51  binary:                                 19
% 7.49/1.51  lits:                                   338
% 7.49/1.51  lits_eq:                                1
% 7.49/1.51  fd_pure:                                0
% 7.49/1.51  fd_pseudo:                              0
% 7.49/1.51  fd_cond:                                0
% 7.49/1.51  fd_pseudo_cond:                         1
% 7.49/1.51  ac_symbols:                             0
% 7.49/1.51  
% 7.49/1.51  ------ Propositional Solver
% 7.49/1.51  
% 7.49/1.51  prop_solver_calls:                      26
% 7.49/1.51  prop_fast_solver_calls:                 8001
% 7.49/1.51  smt_solver_calls:                       0
% 7.49/1.51  smt_fast_solver_calls:                  0
% 7.49/1.51  prop_num_of_clauses:                    5490
% 7.49/1.51  prop_preprocess_simplified:             14270
% 7.49/1.51  prop_fo_subsumed:                       359
% 7.49/1.51  prop_solver_time:                       0.
% 7.49/1.51  smt_solver_time:                        0.
% 7.49/1.51  smt_fast_solver_time:                   0.
% 7.49/1.51  prop_fast_solver_time:                  0.
% 7.49/1.51  prop_unsat_core_time:                   0.
% 7.49/1.51  
% 7.49/1.51  ------ QBF
% 7.49/1.51  
% 7.49/1.51  qbf_q_res:                              0
% 7.49/1.51  qbf_num_tautologies:                    0
% 7.49/1.51  qbf_prep_cycles:                        0
% 7.49/1.51  
% 7.49/1.51  ------ BMC1
% 7.49/1.51  
% 7.49/1.51  bmc1_current_bound:                     -1
% 7.49/1.51  bmc1_last_solved_bound:                 -1
% 7.49/1.51  bmc1_unsat_core_size:                   -1
% 7.49/1.51  bmc1_unsat_core_parents_size:           -1
% 7.49/1.51  bmc1_merge_next_fun:                    0
% 7.49/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.51  
% 7.49/1.51  ------ Instantiation
% 7.49/1.51  
% 7.49/1.51  inst_num_of_clauses:                    1128
% 7.49/1.51  inst_num_in_passive:                    52
% 7.49/1.51  inst_num_in_active:                     539
% 7.49/1.51  inst_num_in_unprocessed:                537
% 7.49/1.51  inst_num_of_loops:                      620
% 7.49/1.51  inst_num_of_learning_restarts:          0
% 7.49/1.51  inst_num_moves_active_passive:          76
% 7.49/1.51  inst_lit_activity:                      0
% 7.49/1.51  inst_lit_activity_moves:                0
% 7.49/1.51  inst_num_tautologies:                   0
% 7.49/1.51  inst_num_prop_implied:                  0
% 7.49/1.51  inst_num_existing_simplified:           0
% 7.49/1.51  inst_num_eq_res_simplified:             0
% 7.49/1.51  inst_num_child_elim:                    0
% 7.49/1.51  inst_num_of_dismatching_blockings:      46
% 7.49/1.51  inst_num_of_non_proper_insts:           833
% 7.49/1.51  inst_num_of_duplicates:                 0
% 7.49/1.51  inst_inst_num_from_inst_to_res:         0
% 7.49/1.51  inst_dismatching_checking_time:         0.
% 7.49/1.51  
% 7.49/1.51  ------ Resolution
% 7.49/1.51  
% 7.49/1.51  res_num_of_clauses:                     0
% 7.49/1.51  res_num_in_passive:                     0
% 7.49/1.51  res_num_in_active:                      0
% 7.49/1.51  res_num_of_loops:                       255
% 7.49/1.51  res_forward_subset_subsumed:            36
% 7.49/1.51  res_backward_subset_subsumed:           0
% 7.49/1.51  res_forward_subsumed:                   0
% 7.49/1.51  res_backward_subsumed:                  0
% 7.49/1.51  res_forward_subsumption_resolution:     0
% 7.49/1.51  res_backward_subsumption_resolution:    0
% 7.49/1.51  res_clause_to_clause_subsumption:       767
% 7.49/1.51  res_orphan_elimination:                 0
% 7.49/1.51  res_tautology_del:                      86
% 7.49/1.51  res_num_eq_res_simplified:              0
% 7.49/1.51  res_num_sel_changes:                    0
% 7.49/1.51  res_moves_from_active_to_pass:          0
% 7.49/1.51  
% 7.49/1.51  ------ Superposition
% 7.49/1.51  
% 7.49/1.51  sup_time_total:                         0.
% 7.49/1.51  sup_time_generating:                    0.
% 7.49/1.51  sup_time_sim_full:                      0.
% 7.49/1.51  sup_time_sim_immed:                     0.
% 7.49/1.51  
% 7.49/1.51  sup_num_of_clauses:                     148
% 7.49/1.51  sup_num_in_active:                      121
% 7.49/1.51  sup_num_in_passive:                     27
% 7.49/1.51  sup_num_of_loops:                       122
% 7.49/1.51  sup_fw_superposition:                   65
% 7.49/1.51  sup_bw_superposition:                   68
% 7.49/1.51  sup_immediate_simplified:               22
% 7.49/1.51  sup_given_eliminated:                   0
% 7.49/1.51  comparisons_done:                       0
% 7.49/1.51  comparisons_avoided:                    0
% 7.49/1.51  
% 7.49/1.51  ------ Simplifications
% 7.49/1.51  
% 7.49/1.51  
% 7.49/1.51  sim_fw_subset_subsumed:                 4
% 7.49/1.51  sim_bw_subset_subsumed:                 2
% 7.49/1.51  sim_fw_subsumed:                        15
% 7.49/1.51  sim_bw_subsumed:                        0
% 7.49/1.51  sim_fw_subsumption_res:                 67
% 7.49/1.51  sim_bw_subsumption_res:                 0
% 7.49/1.51  sim_tautology_del:                      9
% 7.49/1.51  sim_eq_tautology_del:                   12
% 7.49/1.51  sim_eq_res_simp:                        0
% 7.49/1.51  sim_fw_demodulated:                     2
% 7.49/1.51  sim_bw_demodulated:                     0
% 7.49/1.51  sim_light_normalised:                   4
% 7.49/1.51  sim_joinable_taut:                      0
% 7.49/1.51  sim_joinable_simp:                      0
% 7.49/1.51  sim_ac_normalised:                      0
% 7.49/1.51  sim_smt_subsumption:                    0
% 7.49/1.51  
%------------------------------------------------------------------------------
