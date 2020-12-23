%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:17 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 525 expanded)
%              Number of clauses        :  105 ( 108 expanded)
%              Number of leaves         :   10 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          : 1240 (16234 expanded)
%              Number of equality atoms :   90 (  90 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   78 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f18])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f15])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
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
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(definition_folding,[],[f6,f12,f11])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
            | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(X4) )
          & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
              & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
              & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
              & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
            | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              & v1_funct_1(X4) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),X3,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6))
          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),X2,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),u1_struct_0(X2),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6))
          | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(sK6,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(sK6) )
        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),X3,X1)
            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6))
            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),X2,X1)
            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6)) )
          | ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(sK6,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(sK6) ) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(X4) )
              & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                  & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                  & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                  & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                  & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                  & v1_funct_1(X4) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),sK5,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4))
              | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),X2,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,sK5),X1)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
              | ~ v1_funct_1(X4) )
            & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),sK5,X1)
                & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4))
                & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),X2,X1)
                & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4)) )
              | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                & v5_pre_topc(X4,k1_tsep_1(X0,X2,sK5),X1)
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                & v1_funct_1(X4) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & v1_tsep_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                    | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(X4) )
                  & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                      & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                      & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                      & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                    | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & v1_tsep_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_tsep_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),X3,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4))
                  | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),sK4,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X0,sK4,X3),X1)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                  | ~ v1_funct_1(X4) )
                & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),X3,X1)
                    & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4))
                    & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),sK4,X1)
                    & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4)) )
                  | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                    & v5_pre_topc(X4,k1_tsep_1(X0,sK4,X3),X1)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                    & v1_funct_1(X4) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_tsep_1(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),X3,sK3)
                      | ~ v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                      | ~ v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4))
                      | ~ m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),X2,sK3)
                      | ~ v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                      | ~ v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),sK3)
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                      | ~ v1_funct_1(X4) )
                    & ( ( m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),X3,sK3)
                        & v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4))
                        & m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                        & v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),X2,sK3)
                        & v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3))
                        & v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4)) )
                      | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),sK3)
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                        & v1_funct_1(X4) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_tsep_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_tsep_1(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6) )
    & ( ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
        & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
        & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
        & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) )
      | ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
        & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        & v1_funct_1(sK6) ) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_tsep_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26,f25,f24,f23,f22])).

fof(f91,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1999,plain,
    ( sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(X0_50))
    | ~ v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),X1_50,X0_50)
    | ~ v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),X2_50,X0_50)
    | ~ m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
    | ~ m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X0_50))))
    | ~ v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51))
    | ~ v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2429,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_2430,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) = iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1998,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2405,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_2427,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2405])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1997,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2406,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2425,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1996,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2407,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_2423,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1994,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2408,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_2421,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2408])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1993,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),X2_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2409,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_2419,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1992,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2410,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2417,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2410])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1995,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2411,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2415,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1991,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2412,plain,
    ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2413,plain,
    ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2000,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))
    | ~ v5_pre_topc(X0_51,k1_tsep_1(X0_50,X1_50,X2_50),X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2301,plain,
    ( ~ sP1(sK2,sK4,X0_51,sK5,X0_50)
    | sP0(X0_50,sK5,X0_51,sK4,sK2)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))
    | ~ v5_pre_topc(X0_51,k1_tsep_1(sK2,sK4,sK5),X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))))
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2398,plain,
    ( ~ sP1(sK2,sK4,sK6,sK5,sK3)
    | sP0(sK3,sK5,sK6,sK4,sK2)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_2399,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3) != iProver_top
    | sP0(sK3,sK5,sK6,sK4,sK2) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_1,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2003,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | v5_pre_topc(X0_51,k1_tsep_1(X0_50,X1_50,X2_50),X3_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2303,plain,
    ( ~ sP1(sK2,sK4,X0_51,sK5,X0_50)
    | ~ sP0(X0_50,sK5,X0_51,sK4,sK2)
    | v5_pre_topc(X0_51,k1_tsep_1(sK2,sK4,sK5),X0_50) ),
    inference(instantiation,[status(thm)],[c_2003])).

cnf(c_2392,plain,
    ( ~ sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ sP0(sK3,sK5,sK6,sK4,sK2)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_2393,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3) != iProver_top
    | sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X0,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_tsep_1(X2,X0)
    | ~ v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_620,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_tsep_1(X1,X0)
    | ~ v1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

cnf(c_1966,plain,
    ( sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))
    | ~ v1_tsep_1(X1_50,X0_50)
    | ~ v1_tsep_1(X2_50,X0_50)
    | ~ m1_pre_topc(X1_50,X0_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(X3_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_2191,plain,
    ( sP1(sK2,sK4,X0_51,X0_50,X1_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK4,X0_50)),u1_struct_0(X1_50))
    | ~ v1_tsep_1(X0_50,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_50)),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_2211,plain,
    ( sP1(sK2,sK4,X0_51,sK5,X0_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_2381,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_2382,plain,
    ( sP1(sK2,sK4,sK6,sK5,sK3) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK5,sK2) != iProver_top
    | v1_tsep_1(sK4,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2381])).

cnf(c_16,negated_conjecture,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_50,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_424,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_51,c_50,c_49])).

cnf(c_425,negated_conjecture,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_426,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) != iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_109,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_22,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_105,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) = iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_101,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_97,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_93,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_89,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) = iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_85,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_46,negated_conjecture,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_81,plain,
    ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_78,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_77,plain,
    ( v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_76,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_52,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_75,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_53,negated_conjecture,
    ( v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_74,plain,
    ( v1_tsep_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_54,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_73,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_55,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_72,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_56,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_71,plain,
    ( v1_tsep_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_57,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_70,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_58,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_69,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_59,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_68,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_60,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_67,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_61,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_66,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_62,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_65,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_63,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_64,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2430,c_2427,c_2425,c_2423,c_2421,c_2419,c_2417,c_2415,c_2413,c_2399,c_2393,c_2382,c_426,c_109,c_105,c_101,c_97,c_93,c_89,c_85,c_81,c_78,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68,c_67,c_66,c_65,c_64])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.72/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/0.99  
% 1.72/0.99  ------  iProver source info
% 1.72/0.99  
% 1.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/0.99  git: non_committed_changes: false
% 1.72/0.99  git: last_make_outside_of_git: false
% 1.72/0.99  
% 1.72/0.99  ------ 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options
% 1.72/0.99  
% 1.72/0.99  --out_options                           all
% 1.72/0.99  --tptp_safe_out                         true
% 1.72/0.99  --problem_path                          ""
% 1.72/0.99  --include_path                          ""
% 1.72/0.99  --clausifier                            res/vclausify_rel
% 1.72/0.99  --clausifier_options                    --mode clausify
% 1.72/0.99  --stdin                                 false
% 1.72/0.99  --stats_out                             all
% 1.72/0.99  
% 1.72/0.99  ------ General Options
% 1.72/0.99  
% 1.72/0.99  --fof                                   false
% 1.72/0.99  --time_out_real                         305.
% 1.72/0.99  --time_out_virtual                      -1.
% 1.72/0.99  --symbol_type_check                     false
% 1.72/0.99  --clausify_out                          false
% 1.72/0.99  --sig_cnt_out                           false
% 1.72/0.99  --trig_cnt_out                          false
% 1.72/0.99  --trig_cnt_out_tolerance                1.
% 1.72/0.99  --trig_cnt_out_sk_spl                   false
% 1.72/0.99  --abstr_cl_out                          false
% 1.72/0.99  
% 1.72/0.99  ------ Global Options
% 1.72/0.99  
% 1.72/0.99  --schedule                              default
% 1.72/0.99  --add_important_lit                     false
% 1.72/0.99  --prop_solver_per_cl                    1000
% 1.72/0.99  --min_unsat_core                        false
% 1.72/0.99  --soft_assumptions                      false
% 1.72/0.99  --soft_lemma_size                       3
% 1.72/0.99  --prop_impl_unit_size                   0
% 1.72/0.99  --prop_impl_unit                        []
% 1.72/0.99  --share_sel_clauses                     true
% 1.72/0.99  --reset_solvers                         false
% 1.72/0.99  --bc_imp_inh                            [conj_cone]
% 1.72/0.99  --conj_cone_tolerance                   3.
% 1.72/0.99  --extra_neg_conj                        none
% 1.72/0.99  --large_theory_mode                     true
% 1.72/0.99  --prolific_symb_bound                   200
% 1.72/0.99  --lt_threshold                          2000
% 1.72/0.99  --clause_weak_htbl                      true
% 1.72/0.99  --gc_record_bc_elim                     false
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing Options
% 1.72/0.99  
% 1.72/0.99  --preprocessing_flag                    true
% 1.72/0.99  --time_out_prep_mult                    0.1
% 1.72/0.99  --splitting_mode                        input
% 1.72/0.99  --splitting_grd                         true
% 1.72/0.99  --splitting_cvd                         false
% 1.72/0.99  --splitting_cvd_svl                     false
% 1.72/0.99  --splitting_nvd                         32
% 1.72/0.99  --sub_typing                            true
% 1.72/0.99  --prep_gs_sim                           true
% 1.72/0.99  --prep_unflatten                        true
% 1.72/0.99  --prep_res_sim                          true
% 1.72/0.99  --prep_upred                            true
% 1.72/0.99  --prep_sem_filter                       exhaustive
% 1.72/0.99  --prep_sem_filter_out                   false
% 1.72/0.99  --pred_elim                             true
% 1.72/0.99  --res_sim_input                         true
% 1.72/0.99  --eq_ax_congr_red                       true
% 1.72/0.99  --pure_diseq_elim                       true
% 1.72/0.99  --brand_transform                       false
% 1.72/0.99  --non_eq_to_eq                          false
% 1.72/0.99  --prep_def_merge                        true
% 1.72/0.99  --prep_def_merge_prop_impl              false
% 1.72/0.99  --prep_def_merge_mbd                    true
% 1.72/0.99  --prep_def_merge_tr_red                 false
% 1.72/0.99  --prep_def_merge_tr_cl                  false
% 1.72/0.99  --smt_preprocessing                     true
% 1.72/0.99  --smt_ac_axioms                         fast
% 1.72/0.99  --preprocessed_out                      false
% 1.72/0.99  --preprocessed_stats                    false
% 1.72/0.99  
% 1.72/0.99  ------ Abstraction refinement Options
% 1.72/0.99  
% 1.72/0.99  --abstr_ref                             []
% 1.72/0.99  --abstr_ref_prep                        false
% 1.72/0.99  --abstr_ref_until_sat                   false
% 1.72/0.99  --abstr_ref_sig_restrict                funpre
% 1.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/0.99  --abstr_ref_under                       []
% 1.72/0.99  
% 1.72/0.99  ------ SAT Options
% 1.72/0.99  
% 1.72/0.99  --sat_mode                              false
% 1.72/0.99  --sat_fm_restart_options                ""
% 1.72/0.99  --sat_gr_def                            false
% 1.72/0.99  --sat_epr_types                         true
% 1.72/0.99  --sat_non_cyclic_types                  false
% 1.72/0.99  --sat_finite_models                     false
% 1.72/0.99  --sat_fm_lemmas                         false
% 1.72/0.99  --sat_fm_prep                           false
% 1.72/0.99  --sat_fm_uc_incr                        true
% 1.72/0.99  --sat_out_model                         small
% 1.72/0.99  --sat_out_clauses                       false
% 1.72/0.99  
% 1.72/0.99  ------ QBF Options
% 1.72/0.99  
% 1.72/0.99  --qbf_mode                              false
% 1.72/0.99  --qbf_elim_univ                         false
% 1.72/0.99  --qbf_dom_inst                          none
% 1.72/0.99  --qbf_dom_pre_inst                      false
% 1.72/0.99  --qbf_sk_in                             false
% 1.72/0.99  --qbf_pred_elim                         true
% 1.72/0.99  --qbf_split                             512
% 1.72/0.99  
% 1.72/0.99  ------ BMC1 Options
% 1.72/0.99  
% 1.72/0.99  --bmc1_incremental                      false
% 1.72/0.99  --bmc1_axioms                           reachable_all
% 1.72/0.99  --bmc1_min_bound                        0
% 1.72/0.99  --bmc1_max_bound                        -1
% 1.72/0.99  --bmc1_max_bound_default                -1
% 1.72/0.99  --bmc1_symbol_reachability              true
% 1.72/0.99  --bmc1_property_lemmas                  false
% 1.72/0.99  --bmc1_k_induction                      false
% 1.72/0.99  --bmc1_non_equiv_states                 false
% 1.72/0.99  --bmc1_deadlock                         false
% 1.72/0.99  --bmc1_ucm                              false
% 1.72/0.99  --bmc1_add_unsat_core                   none
% 1.72/0.99  --bmc1_unsat_core_children              false
% 1.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/0.99  --bmc1_out_stat                         full
% 1.72/0.99  --bmc1_ground_init                      false
% 1.72/0.99  --bmc1_pre_inst_next_state              false
% 1.72/0.99  --bmc1_pre_inst_state                   false
% 1.72/0.99  --bmc1_pre_inst_reach_state             false
% 1.72/0.99  --bmc1_out_unsat_core                   false
% 1.72/0.99  --bmc1_aig_witness_out                  false
% 1.72/0.99  --bmc1_verbose                          false
% 1.72/0.99  --bmc1_dump_clauses_tptp                false
% 1.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.72/0.99  --bmc1_dump_file                        -
% 1.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.72/0.99  --bmc1_ucm_extend_mode                  1
% 1.72/0.99  --bmc1_ucm_init_mode                    2
% 1.72/0.99  --bmc1_ucm_cone_mode                    none
% 1.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.72/0.99  --bmc1_ucm_relax_model                  4
% 1.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/0.99  --bmc1_ucm_layered_model                none
% 1.72/0.99  --bmc1_ucm_max_lemma_size               10
% 1.72/0.99  
% 1.72/0.99  ------ AIG Options
% 1.72/0.99  
% 1.72/0.99  --aig_mode                              false
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation Options
% 1.72/0.99  
% 1.72/0.99  --instantiation_flag                    true
% 1.72/0.99  --inst_sos_flag                         false
% 1.72/0.99  --inst_sos_phase                        true
% 1.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel_side                     num_symb
% 1.72/0.99  --inst_solver_per_active                1400
% 1.72/0.99  --inst_solver_calls_frac                1.
% 1.72/0.99  --inst_passive_queue_type               priority_queues
% 1.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/0.99  --inst_passive_queues_freq              [25;2]
% 1.72/0.99  --inst_dismatching                      true
% 1.72/0.99  --inst_eager_unprocessed_to_passive     true
% 1.72/0.99  --inst_prop_sim_given                   true
% 1.72/0.99  --inst_prop_sim_new                     false
% 1.72/0.99  --inst_subs_new                         false
% 1.72/0.99  --inst_eq_res_simp                      false
% 1.72/0.99  --inst_subs_given                       false
% 1.72/0.99  --inst_orphan_elimination               true
% 1.72/0.99  --inst_learning_loop_flag               true
% 1.72/0.99  --inst_learning_start                   3000
% 1.72/0.99  --inst_learning_factor                  2
% 1.72/0.99  --inst_start_prop_sim_after_learn       3
% 1.72/0.99  --inst_sel_renew                        solver
% 1.72/0.99  --inst_lit_activity_flag                true
% 1.72/0.99  --inst_restr_to_given                   false
% 1.72/0.99  --inst_activity_threshold               500
% 1.72/0.99  --inst_out_proof                        true
% 1.72/0.99  
% 1.72/0.99  ------ Resolution Options
% 1.72/0.99  
% 1.72/0.99  --resolution_flag                       true
% 1.72/0.99  --res_lit_sel                           adaptive
% 1.72/0.99  --res_lit_sel_side                      none
% 1.72/0.99  --res_ordering                          kbo
% 1.72/0.99  --res_to_prop_solver                    active
% 1.72/0.99  --res_prop_simpl_new                    false
% 1.72/0.99  --res_prop_simpl_given                  true
% 1.72/0.99  --res_passive_queue_type                priority_queues
% 1.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/0.99  --res_passive_queues_freq               [15;5]
% 1.72/0.99  --res_forward_subs                      full
% 1.72/0.99  --res_backward_subs                     full
% 1.72/0.99  --res_forward_subs_resolution           true
% 1.72/0.99  --res_backward_subs_resolution          true
% 1.72/0.99  --res_orphan_elimination                true
% 1.72/0.99  --res_time_limit                        2.
% 1.72/0.99  --res_out_proof                         true
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Options
% 1.72/0.99  
% 1.72/0.99  --superposition_flag                    true
% 1.72/0.99  --sup_passive_queue_type                priority_queues
% 1.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.72/0.99  --demod_completeness_check              fast
% 1.72/0.99  --demod_use_ground                      true
% 1.72/0.99  --sup_to_prop_solver                    passive
% 1.72/0.99  --sup_prop_simpl_new                    true
% 1.72/0.99  --sup_prop_simpl_given                  true
% 1.72/0.99  --sup_fun_splitting                     false
% 1.72/0.99  --sup_smt_interval                      50000
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Simplification Setup
% 1.72/0.99  
% 1.72/0.99  --sup_indices_passive                   []
% 1.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_full_bw                           [BwDemod]
% 1.72/0.99  --sup_immed_triv                        [TrivRules]
% 1.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_immed_bw_main                     []
% 1.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  
% 1.72/0.99  ------ Combination Options
% 1.72/0.99  
% 1.72/0.99  --comb_res_mult                         3
% 1.72/0.99  --comb_sup_mult                         2
% 1.72/0.99  --comb_inst_mult                        10
% 1.72/0.99  
% 1.72/0.99  ------ Debug Options
% 1.72/0.99  
% 1.72/0.99  --dbg_backtrace                         false
% 1.72/0.99  --dbg_dump_prop_clauses                 false
% 1.72/0.99  --dbg_dump_prop_clauses_file            -
% 1.72/0.99  --dbg_out_stat                          false
% 1.72/0.99  ------ Parsing...
% 1.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/0.99  ------ Proving...
% 1.72/0.99  ------ Problem Properties 
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  clauses                                 39
% 1.72/0.99  conjectures                             24
% 1.72/0.99  EPR                                     14
% 1.72/0.99  Horn                                    30
% 1.72/0.99  unary                                   15
% 1.72/0.99  binary                                  16
% 1.72/0.99  lits                                    99
% 1.72/0.99  lits eq                                 0
% 1.72/0.99  fd_pure                                 0
% 1.72/0.99  fd_pseudo                               0
% 1.72/0.99  fd_cond                                 0
% 1.72/0.99  fd_pseudo_cond                          0
% 1.72/0.99  AC symbols                              0
% 1.72/0.99  
% 1.72/0.99  ------ Schedule dynamic 5 is on 
% 1.72/0.99  
% 1.72/0.99  ------ no equalities: superposition off 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  ------ 
% 1.72/0.99  Current options:
% 1.72/0.99  ------ 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options
% 1.72/0.99  
% 1.72/0.99  --out_options                           all
% 1.72/0.99  --tptp_safe_out                         true
% 1.72/0.99  --problem_path                          ""
% 1.72/0.99  --include_path                          ""
% 1.72/0.99  --clausifier                            res/vclausify_rel
% 1.72/0.99  --clausifier_options                    --mode clausify
% 1.72/0.99  --stdin                                 false
% 1.72/0.99  --stats_out                             all
% 1.72/0.99  
% 1.72/0.99  ------ General Options
% 1.72/0.99  
% 1.72/0.99  --fof                                   false
% 1.72/0.99  --time_out_real                         305.
% 1.72/0.99  --time_out_virtual                      -1.
% 1.72/0.99  --symbol_type_check                     false
% 1.72/0.99  --clausify_out                          false
% 1.72/0.99  --sig_cnt_out                           false
% 1.72/0.99  --trig_cnt_out                          false
% 1.72/0.99  --trig_cnt_out_tolerance                1.
% 1.72/0.99  --trig_cnt_out_sk_spl                   false
% 1.72/0.99  --abstr_cl_out                          false
% 1.72/0.99  
% 1.72/0.99  ------ Global Options
% 1.72/0.99  
% 1.72/0.99  --schedule                              default
% 1.72/0.99  --add_important_lit                     false
% 1.72/0.99  --prop_solver_per_cl                    1000
% 1.72/0.99  --min_unsat_core                        false
% 1.72/0.99  --soft_assumptions                      false
% 1.72/0.99  --soft_lemma_size                       3
% 1.72/0.99  --prop_impl_unit_size                   0
% 1.72/0.99  --prop_impl_unit                        []
% 1.72/0.99  --share_sel_clauses                     true
% 1.72/0.99  --reset_solvers                         false
% 1.72/0.99  --bc_imp_inh                            [conj_cone]
% 1.72/0.99  --conj_cone_tolerance                   3.
% 1.72/0.99  --extra_neg_conj                        none
% 1.72/0.99  --large_theory_mode                     true
% 1.72/0.99  --prolific_symb_bound                   200
% 1.72/0.99  --lt_threshold                          2000
% 1.72/0.99  --clause_weak_htbl                      true
% 1.72/0.99  --gc_record_bc_elim                     false
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing Options
% 1.72/0.99  
% 1.72/0.99  --preprocessing_flag                    true
% 1.72/0.99  --time_out_prep_mult                    0.1
% 1.72/0.99  --splitting_mode                        input
% 1.72/0.99  --splitting_grd                         true
% 1.72/0.99  --splitting_cvd                         false
% 1.72/0.99  --splitting_cvd_svl                     false
% 1.72/0.99  --splitting_nvd                         32
% 1.72/0.99  --sub_typing                            true
% 1.72/0.99  --prep_gs_sim                           true
% 1.72/0.99  --prep_unflatten                        true
% 1.72/0.99  --prep_res_sim                          true
% 1.72/0.99  --prep_upred                            true
% 1.72/0.99  --prep_sem_filter                       exhaustive
% 1.72/0.99  --prep_sem_filter_out                   false
% 1.72/0.99  --pred_elim                             true
% 1.72/0.99  --res_sim_input                         true
% 1.72/0.99  --eq_ax_congr_red                       true
% 1.72/0.99  --pure_diseq_elim                       true
% 1.72/0.99  --brand_transform                       false
% 1.72/0.99  --non_eq_to_eq                          false
% 1.72/0.99  --prep_def_merge                        true
% 1.72/0.99  --prep_def_merge_prop_impl              false
% 1.72/0.99  --prep_def_merge_mbd                    true
% 1.72/0.99  --prep_def_merge_tr_red                 false
% 1.72/0.99  --prep_def_merge_tr_cl                  false
% 1.72/0.99  --smt_preprocessing                     true
% 1.72/0.99  --smt_ac_axioms                         fast
% 1.72/0.99  --preprocessed_out                      false
% 1.72/0.99  --preprocessed_stats                    false
% 1.72/0.99  
% 1.72/0.99  ------ Abstraction refinement Options
% 1.72/0.99  
% 1.72/0.99  --abstr_ref                             []
% 1.72/0.99  --abstr_ref_prep                        false
% 1.72/0.99  --abstr_ref_until_sat                   false
% 1.72/0.99  --abstr_ref_sig_restrict                funpre
% 1.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/0.99  --abstr_ref_under                       []
% 1.72/0.99  
% 1.72/0.99  ------ SAT Options
% 1.72/0.99  
% 1.72/0.99  --sat_mode                              false
% 1.72/0.99  --sat_fm_restart_options                ""
% 1.72/0.99  --sat_gr_def                            false
% 1.72/0.99  --sat_epr_types                         true
% 1.72/0.99  --sat_non_cyclic_types                  false
% 1.72/0.99  --sat_finite_models                     false
% 1.72/0.99  --sat_fm_lemmas                         false
% 1.72/0.99  --sat_fm_prep                           false
% 1.72/0.99  --sat_fm_uc_incr                        true
% 1.72/0.99  --sat_out_model                         small
% 1.72/0.99  --sat_out_clauses                       false
% 1.72/0.99  
% 1.72/0.99  ------ QBF Options
% 1.72/0.99  
% 1.72/0.99  --qbf_mode                              false
% 1.72/0.99  --qbf_elim_univ                         false
% 1.72/0.99  --qbf_dom_inst                          none
% 1.72/0.99  --qbf_dom_pre_inst                      false
% 1.72/0.99  --qbf_sk_in                             false
% 1.72/0.99  --qbf_pred_elim                         true
% 1.72/0.99  --qbf_split                             512
% 1.72/0.99  
% 1.72/0.99  ------ BMC1 Options
% 1.72/0.99  
% 1.72/0.99  --bmc1_incremental                      false
% 1.72/0.99  --bmc1_axioms                           reachable_all
% 1.72/0.99  --bmc1_min_bound                        0
% 1.72/0.99  --bmc1_max_bound                        -1
% 1.72/0.99  --bmc1_max_bound_default                -1
% 1.72/0.99  --bmc1_symbol_reachability              true
% 1.72/0.99  --bmc1_property_lemmas                  false
% 1.72/0.99  --bmc1_k_induction                      false
% 1.72/0.99  --bmc1_non_equiv_states                 false
% 1.72/0.99  --bmc1_deadlock                         false
% 1.72/0.99  --bmc1_ucm                              false
% 1.72/0.99  --bmc1_add_unsat_core                   none
% 1.72/0.99  --bmc1_unsat_core_children              false
% 1.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/0.99  --bmc1_out_stat                         full
% 1.72/0.99  --bmc1_ground_init                      false
% 1.72/0.99  --bmc1_pre_inst_next_state              false
% 1.72/0.99  --bmc1_pre_inst_state                   false
% 1.72/0.99  --bmc1_pre_inst_reach_state             false
% 1.72/0.99  --bmc1_out_unsat_core                   false
% 1.72/0.99  --bmc1_aig_witness_out                  false
% 1.72/0.99  --bmc1_verbose                          false
% 1.72/0.99  --bmc1_dump_clauses_tptp                false
% 1.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.72/0.99  --bmc1_dump_file                        -
% 1.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.72/0.99  --bmc1_ucm_extend_mode                  1
% 1.72/0.99  --bmc1_ucm_init_mode                    2
% 1.72/0.99  --bmc1_ucm_cone_mode                    none
% 1.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.72/0.99  --bmc1_ucm_relax_model                  4
% 1.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/0.99  --bmc1_ucm_layered_model                none
% 1.72/0.99  --bmc1_ucm_max_lemma_size               10
% 1.72/0.99  
% 1.72/0.99  ------ AIG Options
% 1.72/0.99  
% 1.72/0.99  --aig_mode                              false
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation Options
% 1.72/0.99  
% 1.72/0.99  --instantiation_flag                    true
% 1.72/0.99  --inst_sos_flag                         false
% 1.72/0.99  --inst_sos_phase                        true
% 1.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel_side                     none
% 1.72/0.99  --inst_solver_per_active                1400
% 1.72/0.99  --inst_solver_calls_frac                1.
% 1.72/0.99  --inst_passive_queue_type               priority_queues
% 1.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/0.99  --inst_passive_queues_freq              [25;2]
% 1.72/0.99  --inst_dismatching                      true
% 1.72/0.99  --inst_eager_unprocessed_to_passive     true
% 1.72/0.99  --inst_prop_sim_given                   true
% 1.72/0.99  --inst_prop_sim_new                     false
% 1.72/0.99  --inst_subs_new                         false
% 1.72/0.99  --inst_eq_res_simp                      false
% 1.72/0.99  --inst_subs_given                       false
% 1.72/0.99  --inst_orphan_elimination               true
% 1.72/0.99  --inst_learning_loop_flag               true
% 1.72/0.99  --inst_learning_start                   3000
% 1.72/0.99  --inst_learning_factor                  2
% 1.72/0.99  --inst_start_prop_sim_after_learn       3
% 1.72/0.99  --inst_sel_renew                        solver
% 1.72/0.99  --inst_lit_activity_flag                true
% 1.72/0.99  --inst_restr_to_given                   false
% 1.72/0.99  --inst_activity_threshold               500
% 1.72/0.99  --inst_out_proof                        true
% 1.72/0.99  
% 1.72/0.99  ------ Resolution Options
% 1.72/0.99  
% 1.72/0.99  --resolution_flag                       false
% 1.72/0.99  --res_lit_sel                           adaptive
% 1.72/0.99  --res_lit_sel_side                      none
% 1.72/0.99  --res_ordering                          kbo
% 1.72/0.99  --res_to_prop_solver                    active
% 1.72/0.99  --res_prop_simpl_new                    false
% 1.72/0.99  --res_prop_simpl_given                  true
% 1.72/0.99  --res_passive_queue_type                priority_queues
% 1.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/0.99  --res_passive_queues_freq               [15;5]
% 1.72/0.99  --res_forward_subs                      full
% 1.72/0.99  --res_backward_subs                     full
% 1.72/0.99  --res_forward_subs_resolution           true
% 1.72/0.99  --res_backward_subs_resolution          true
% 1.72/0.99  --res_orphan_elimination                true
% 1.72/0.99  --res_time_limit                        2.
% 1.72/0.99  --res_out_proof                         true
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Options
% 1.72/0.99  
% 1.72/0.99  --superposition_flag                    false
% 1.72/0.99  --sup_passive_queue_type                priority_queues
% 1.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.72/0.99  --demod_completeness_check              fast
% 1.72/0.99  --demod_use_ground                      true
% 1.72/0.99  --sup_to_prop_solver                    passive
% 1.72/0.99  --sup_prop_simpl_new                    true
% 1.72/0.99  --sup_prop_simpl_given                  true
% 1.72/0.99  --sup_fun_splitting                     false
% 1.72/0.99  --sup_smt_interval                      50000
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Simplification Setup
% 1.72/0.99  
% 1.72/0.99  --sup_indices_passive                   []
% 1.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_full_bw                           [BwDemod]
% 1.72/0.99  --sup_immed_triv                        [TrivRules]
% 1.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_immed_bw_main                     []
% 1.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  
% 1.72/0.99  ------ Combination Options
% 1.72/0.99  
% 1.72/0.99  --comb_res_mult                         3
% 1.72/0.99  --comb_sup_mult                         2
% 1.72/0.99  --comb_inst_mult                        10
% 1.72/0.99  
% 1.72/0.99  ------ Debug Options
% 1.72/0.99  
% 1.72/0.99  --dbg_backtrace                         false
% 1.72/0.99  --dbg_dump_prop_clauses                 false
% 1.72/0.99  --dbg_dump_prop_clauses_file            -
% 1.72/0.99  --dbg_out_stat                          false
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  ------ Proving...
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  % SZS status Theorem for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  fof(f11,plain,(
% 1.72/0.99    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 1.72/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.72/0.99  
% 1.72/0.99  fof(f17,plain,(
% 1.72/0.99    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 1.72/0.99    inference(nnf_transformation,[],[f11])).
% 1.72/0.99  
% 1.72/0.99  fof(f18,plain,(
% 1.72/0.99    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 1.72/0.99    inference(flattening,[],[f17])).
% 1.72/0.99  
% 1.72/0.99  fof(f19,plain,(
% 1.72/0.99    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.72/0.99    inference(rectify,[],[f18])).
% 1.72/0.99  
% 1.72/0.99  fof(f41,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f40,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f39,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f38,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f36,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f35,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f34,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f37,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f33,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f12,plain,(
% 1.72/0.99    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 1.72/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.72/0.99  
% 1.72/0.99  fof(f14,plain,(
% 1.72/0.99    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 1.72/0.99    inference(nnf_transformation,[],[f12])).
% 1.72/0.99  
% 1.72/0.99  fof(f15,plain,(
% 1.72/0.99    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 1.72/0.99    inference(flattening,[],[f14])).
% 1.72/0.99  
% 1.72/0.99  fof(f16,plain,(
% 1.72/0.99    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 1.72/0.99    inference(rectify,[],[f15])).
% 1.72/0.99  
% 1.72/0.99  fof(f28,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f16])).
% 1.72/0.99  
% 1.72/0.99  fof(f31,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f16])).
% 1.72/0.99  
% 1.72/0.99  fof(f1,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f5,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f1])).
% 1.72/0.99  
% 1.72/0.99  fof(f6,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f5])).
% 1.72/0.99  
% 1.72/0.99  fof(f13,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(definition_folding,[],[f6,f12,f11])).
% 1.72/0.99  
% 1.72/0.99  fof(f42,plain,(
% 1.72/0.99    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f13])).
% 1.72/0.99  
% 1.72/0.99  fof(f2,axiom,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f7,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f2])).
% 1.72/0.99  
% 1.72/0.99  fof(f8,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f7])).
% 1.72/0.99  
% 1.72/0.99  fof(f43,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f8])).
% 1.72/0.99  
% 1.72/0.99  fof(f3,conjecture,(
% 1.72/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f4,negated_conjecture,(
% 1.72/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 1.72/0.99    inference(negated_conjecture,[],[f3])).
% 1.72/0.99  
% 1.72/0.99  fof(f9,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <~> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f4])).
% 1.72/0.99  
% 1.72/0.99  fof(f10,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <~> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f9])).
% 1.72/0.99  
% 1.72/0.99  fof(f20,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.99    inference(nnf_transformation,[],[f10])).
% 1.72/0.99  
% 1.72/0.99  fof(f21,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.99    inference(flattening,[],[f20])).
% 1.72/0.99  
% 1.72/0.99  fof(f26,plain,(
% 1.72/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(sK6,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(sK6)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK6)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK6))) | (m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(sK6,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f25,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),sK5,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,sK5),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),sK5,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,sK5),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f24,plain,(
% 1.72/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),sK4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,sK4,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),sK4,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,sK4,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f23,plain,(
% 1.72/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),X3,sK3) | ~v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),X2,sK3) | ~v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),X3,sK3) & v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),X2,sK3) & v1_funct_2(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f22,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f27,plain,(
% 1.72/0.99    (((((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))) | (m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & v1_tsep_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26,f25,f24,f23,f22])).
% 1.72/0.99  
% 1.72/0.99  fof(f91,plain,(
% 1.72/0.99    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f56,plain,(
% 1.72/0.99    v1_funct_1(sK6)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f57,plain,(
% 1.72/0.99    v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f58,plain,(
% 1.72/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f89,plain,(
% 1.72/0.99    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f85,plain,(
% 1.72/0.99    v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f81,plain,(
% 1.72/0.99    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f77,plain,(
% 1.72/0.99    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f73,plain,(
% 1.72/0.99    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f69,plain,(
% 1.72/0.99    v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f65,plain,(
% 1.72/0.99    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f61,plain,(
% 1.72/0.99    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f55,plain,(
% 1.72/0.99    m1_pre_topc(sK5,sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f54,plain,(
% 1.72/0.99    v1_tsep_1(sK5,sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f53,plain,(
% 1.72/0.99    ~v2_struct_0(sK5)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f52,plain,(
% 1.72/0.99    m1_pre_topc(sK4,sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f51,plain,(
% 1.72/0.99    v1_tsep_1(sK4,sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f50,plain,(
% 1.72/0.99    ~v2_struct_0(sK4)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f49,plain,(
% 1.72/0.99    l1_pre_topc(sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f48,plain,(
% 1.72/0.99    v2_pre_topc(sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f47,plain,(
% 1.72/0.99    ~v2_struct_0(sK3)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f46,plain,(
% 1.72/0.99    l1_pre_topc(sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f45,plain,(
% 1.72/0.99    v2_pre_topc(sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f44,plain,(
% 1.72/0.99    ~v2_struct_0(sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  cnf(c_5,plain,
% 1.72/0.99      ( sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1999,plain,
% 1.72/0.99      ( sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),u1_struct_0(X1_50),u1_struct_0(X0_50))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(X0_50))
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),X1_50,X0_50)
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),X2_50,X0_50)
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X0_50))))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51)) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2429,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1999]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2430,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) = iProver_top
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) != iProver_top
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) != iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) != iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_6,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1998,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2405,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1998]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2427,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2405]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_7,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1997,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),X1_50,X0_50) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2406,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1997]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2425,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_8,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1996,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2407,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1996]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2423,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_10,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1994,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X0_50)))) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2408,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1994]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2421,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2408]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_11,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1993,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),X2_50,X0_50) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2409,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1993]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2419,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_12,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1992,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | v1_funct_2(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(X0_50)) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2410,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1992]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2417,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2410]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_9,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1995,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X1_50,X0_51)) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2411,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1995]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2415,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_13,plain,
% 1.72/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1991,plain,
% 1.72/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(X3_50,X0_50,k1_tsep_1(X3_50,X2_50,X1_50),X2_50,X0_51)) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2412,plain,
% 1.72/0.99      ( ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1991]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2413,plain,
% 1.72/0.99      ( sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_4,plain,
% 1.72/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.72/0.99      | sP0(X4,X3,X2,X1,X0)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 1.72/0.99      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 1.72/0.99      | ~ v1_funct_1(X2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2000,plain,
% 1.72/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.72/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))
% 1.72/0.99      | ~ v5_pre_topc(X0_51,k1_tsep_1(X0_50,X1_50,X2_50),X3_50)
% 1.72/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))))
% 1.72/0.99      | ~ v1_funct_1(X0_51) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2301,plain,
% 1.72/0.99      ( ~ sP1(sK2,sK4,X0_51,sK5,X0_50)
% 1.72/0.99      | sP0(X0_50,sK5,X0_51,sK4,sK2)
% 1.72/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))
% 1.72/0.99      | ~ v5_pre_topc(X0_51,k1_tsep_1(sK2,sK4,sK5),X0_50)
% 1.72/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))))
% 1.72/0.99      | ~ v1_funct_1(X0_51) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2000]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2398,plain,
% 1.72/0.99      ( ~ sP1(sK2,sK4,sK6,sK5,sK3)
% 1.72/0.99      | sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 1.72/0.99      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 1.72/0.99      | ~ v1_funct_1(sK6) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2301]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2399,plain,
% 1.72/0.99      ( sP1(sK2,sK4,sK6,sK5,sK3) != iProver_top
% 1.72/0.99      | sP0(sK3,sK5,sK6,sK4,sK2) = iProver_top
% 1.72/0.99      | v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 1.72/0.99      | v1_funct_1(sK6) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1,plain,
% 1.72/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.72/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 1.72/0.99      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 1.72/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2003,plain,
% 1.72/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.72/0.99      | v5_pre_topc(X0_51,k1_tsep_1(X0_50,X1_50,X2_50),X3_50) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2303,plain,
% 1.72/0.99      ( ~ sP1(sK2,sK4,X0_51,sK5,X0_50)
% 1.72/0.99      | ~ sP0(X0_50,sK5,X0_51,sK4,sK2)
% 1.72/0.99      | v5_pre_topc(X0_51,k1_tsep_1(sK2,sK4,sK5),X0_50) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2003]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2392,plain,
% 1.72/0.99      ( ~ sP1(sK2,sK4,sK6,sK5,sK3)
% 1.72/0.99      | ~ sP0(sK3,sK5,sK6,sK4,sK2)
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2303]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2393,plain,
% 1.72/0.99      ( sP1(sK2,sK4,sK6,sK5,sK3) != iProver_top
% 1.72/0.99      | sP0(sK3,sK5,sK6,sK4,sK2) != iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_14,plain,
% 1.72/0.99      ( sP1(X0,X1,X2,X3,X4)
% 1.72/0.99      | ~ r4_tsep_1(X0,X1,X3)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 1.72/0.99      | ~ m1_pre_topc(X3,X0)
% 1.72/0.99      | ~ m1_pre_topc(X1,X0)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 1.72/0.99      | ~ v2_pre_topc(X4)
% 1.72/0.99      | ~ v2_pre_topc(X0)
% 1.72/0.99      | ~ l1_pre_topc(X4)
% 1.72/0.99      | ~ l1_pre_topc(X0)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | ~ v1_funct_1(X2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_15,plain,
% 1.72/0.99      ( r4_tsep_1(X0,X1,X2)
% 1.72/0.99      | ~ v1_tsep_1(X2,X0)
% 1.72/0.99      | ~ v1_tsep_1(X1,X0)
% 1.72/0.99      | ~ m1_pre_topc(X2,X0)
% 1.72/0.99      | ~ m1_pre_topc(X1,X0)
% 1.72/0.99      | ~ v2_pre_topc(X0)
% 1.72/0.99      | ~ l1_pre_topc(X0)
% 1.72/0.99      | v2_struct_0(X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_620,plain,
% 1.72/0.99      ( sP1(X0,X1,X2,X3,X4)
% 1.72/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 1.72/0.99      | ~ v1_tsep_1(X1,X0)
% 1.72/0.99      | ~ v1_tsep_1(X3,X0)
% 1.72/0.99      | ~ m1_pre_topc(X3,X0)
% 1.72/0.99      | ~ m1_pre_topc(X1,X0)
% 1.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 1.72/0.99      | ~ v2_pre_topc(X4)
% 1.72/0.99      | ~ v2_pre_topc(X0)
% 1.72/0.99      | ~ l1_pre_topc(X4)
% 1.72/0.99      | ~ l1_pre_topc(X0)
% 1.72/0.99      | v2_struct_0(X1)
% 1.72/0.99      | v2_struct_0(X0)
% 1.72/0.99      | v2_struct_0(X3)
% 1.72/0.99      | v2_struct_0(X4)
% 1.72/0.99      | ~ v1_funct_1(X2) ),
% 1.72/0.99      inference(resolution,[status(thm)],[c_14,c_15]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1966,plain,
% 1.72/0.99      ( sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.72/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))
% 1.72/0.99      | ~ v1_tsep_1(X1_50,X0_50)
% 1.72/0.99      | ~ v1_tsep_1(X2_50,X0_50)
% 1.72/0.99      | ~ m1_pre_topc(X1_50,X0_50)
% 1.72/0.99      | ~ m1_pre_topc(X2_50,X0_50)
% 1.72/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_50,X1_50,X2_50)),u1_struct_0(X3_50))))
% 1.72/0.99      | ~ v2_pre_topc(X0_50)
% 1.72/0.99      | ~ v2_pre_topc(X3_50)
% 1.72/0.99      | ~ l1_pre_topc(X0_50)
% 1.72/0.99      | ~ l1_pre_topc(X3_50)
% 1.72/0.99      | v2_struct_0(X1_50)
% 1.72/0.99      | v2_struct_0(X0_50)
% 1.72/0.99      | v2_struct_0(X3_50)
% 1.72/0.99      | v2_struct_0(X2_50)
% 1.72/0.99      | ~ v1_funct_1(X0_51) ),
% 1.72/0.99      inference(subtyping,[status(esa)],[c_620]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2191,plain,
% 1.72/0.99      ( sP1(sK2,sK4,X0_51,X0_50,X1_50)
% 1.72/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK4,X0_50)),u1_struct_0(X1_50))
% 1.72/0.99      | ~ v1_tsep_1(X0_50,sK2)
% 1.72/0.99      | ~ v1_tsep_1(sK4,sK2)
% 1.72/0.99      | ~ m1_pre_topc(X0_50,sK2)
% 1.72/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.72/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_50)),u1_struct_0(X1_50))))
% 1.72/0.99      | ~ v2_pre_topc(X1_50)
% 1.72/0.99      | ~ v2_pre_topc(sK2)
% 1.72/0.99      | ~ l1_pre_topc(X1_50)
% 1.72/0.99      | ~ l1_pre_topc(sK2)
% 1.72/0.99      | v2_struct_0(X1_50)
% 1.72/0.99      | v2_struct_0(X0_50)
% 1.72/0.99      | v2_struct_0(sK4)
% 1.72/0.99      | v2_struct_0(sK2)
% 1.72/0.99      | ~ v1_funct_1(X0_51) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_1966]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2211,plain,
% 1.72/0.99      ( sP1(sK2,sK4,X0_51,sK5,X0_50)
% 1.72/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))
% 1.72/0.99      | ~ v1_tsep_1(sK5,sK2)
% 1.72/0.99      | ~ v1_tsep_1(sK4,sK2)
% 1.72/0.99      | ~ m1_pre_topc(sK5,sK2)
% 1.72/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.72/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_50))))
% 1.72/0.99      | ~ v2_pre_topc(X0_50)
% 1.72/0.99      | ~ v2_pre_topc(sK2)
% 1.72/0.99      | ~ l1_pre_topc(X0_50)
% 1.72/0.99      | ~ l1_pre_topc(sK2)
% 1.72/0.99      | v2_struct_0(X0_50)
% 1.72/0.99      | v2_struct_0(sK5)
% 1.72/0.99      | v2_struct_0(sK4)
% 1.72/0.99      | v2_struct_0(sK2)
% 1.72/0.99      | ~ v1_funct_1(X0_51) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2191]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2381,plain,
% 1.72/0.99      ( sP1(sK2,sK4,sK6,sK5,sK3)
% 1.72/0.99      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 1.72/0.99      | ~ v1_tsep_1(sK5,sK2)
% 1.72/0.99      | ~ v1_tsep_1(sK4,sK2)
% 1.72/0.99      | ~ m1_pre_topc(sK5,sK2)
% 1.72/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.72/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 1.72/0.99      | ~ v2_pre_topc(sK3)
% 1.72/0.99      | ~ v2_pre_topc(sK2)
% 1.72/0.99      | ~ l1_pre_topc(sK3)
% 1.72/0.99      | ~ l1_pre_topc(sK2)
% 1.72/0.99      | v2_struct_0(sK5)
% 1.72/0.99      | v2_struct_0(sK4)
% 1.72/0.99      | v2_struct_0(sK3)
% 1.72/0.99      | v2_struct_0(sK2)
% 1.72/0.99      | ~ v1_funct_1(sK6) ),
% 1.72/0.99      inference(instantiation,[status(thm)],[c_2211]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2382,plain,
% 1.72/0.99      ( sP1(sK2,sK4,sK6,sK5,sK3) = iProver_top
% 1.72/0.99      | v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | v1_tsep_1(sK5,sK2) != iProver_top
% 1.72/0.99      | v1_tsep_1(sK4,sK2) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 1.72/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.72/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK3) != iProver_top
% 1.72/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.72/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.72/0.99      | l1_pre_topc(sK2) != iProver_top
% 1.72/0.99      | v2_struct_0(sK5) = iProver_top
% 1.72/0.99      | v2_struct_0(sK4) = iProver_top
% 1.72/0.99      | v2_struct_0(sK3) = iProver_top
% 1.72/0.99      | v2_struct_0(sK2) = iProver_top
% 1.72/0.99      | v1_funct_1(sK6) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2381]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_16,negated_conjecture,
% 1.72/0.99      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
% 1.72/0.99      | ~ v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
% 1.72/0.99      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 1.72/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
% 1.72/0.99      | ~ v1_funct_1(sK6) ),
% 1.72/0.99      inference(cnf_transformation,[],[f91]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_51,negated_conjecture,
% 1.72/0.99      ( v1_funct_1(sK6) ),
% 1.72/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_50,negated_conjecture,
% 1.72/0.99      ( v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_49,negated_conjecture,
% 1.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_424,plain,
% 1.72/0.99      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
% 1.72/0.99      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 1.72/0.99      inference(global_propositional_subsumption,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_16,c_51,c_50,c_49]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_425,negated_conjecture,
% 1.72/0.99      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.72/0.99      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
% 1.72/0.99      | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
% 1.72/0.99      | ~ v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.72/0.99      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))
% 1.72/0.99      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_424]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_426,plain,
% 1.72/0.99      ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) != iProver_top
% 1.72/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) != iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) != iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_18,negated_conjecture,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f89]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_109,plain,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_22,negated_conjecture,
% 1.72/0.99      ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f85]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_105,plain,
% 1.72/0.99      ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) = iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_26,negated_conjecture,
% 1.72/0.99      ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_101,plain,
% 1.72/0.99      ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_30,negated_conjecture,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_97,plain,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_34,negated_conjecture,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_93,plain,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 1.72/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_38,negated_conjecture,
% 1.72/0.99      ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_89,plain,
% 1.72/0.99      ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) = iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_42,negated_conjecture,
% 1.72/0.99      ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_85,plain,
% 1.72/0.99      ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
% 1.72/0.99      | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_46,negated_conjecture,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) ),
% 1.72/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_81,plain,
% 1.72/0.99      ( v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 1.72/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_78,plain,
% 1.72/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_77,plain,
% 1.72/0.99      ( v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_76,plain,
% 1.72/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_52,negated_conjecture,
% 1.72/0.99      ( m1_pre_topc(sK5,sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_75,plain,
% 1.72/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_53,negated_conjecture,
% 1.72/0.99      ( v1_tsep_1(sK5,sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_74,plain,
% 1.72/0.99      ( v1_tsep_1(sK5,sK2) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_54,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK5) ),
% 1.72/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_73,plain,
% 1.72/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_55,negated_conjecture,
% 1.72/0.99      ( m1_pre_topc(sK4,sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_72,plain,
% 1.72/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_56,negated_conjecture,
% 1.72/0.99      ( v1_tsep_1(sK4,sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_71,plain,
% 1.72/0.99      ( v1_tsep_1(sK4,sK2) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_57,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK4) ),
% 1.72/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_70,plain,
% 1.72/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_58,negated_conjecture,
% 1.72/0.99      ( l1_pre_topc(sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_69,plain,
% 1.72/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_59,negated_conjecture,
% 1.72/0.99      ( v2_pre_topc(sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_68,plain,
% 1.72/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_60,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK3) ),
% 1.72/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_67,plain,
% 1.72/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_61,negated_conjecture,
% 1.72/0.99      ( l1_pre_topc(sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_66,plain,
% 1.72/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_62,negated_conjecture,
% 1.72/0.99      ( v2_pre_topc(sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_65,plain,
% 1.72/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_63,negated_conjecture,
% 1.72/0.99      ( ~ v2_struct_0(sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_64,plain,
% 1.72/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(contradiction,plain,
% 1.72/0.99      ( $false ),
% 1.72/0.99      inference(minisat,
% 1.72/0.99                [status(thm)],
% 1.72/0.99                [c_2430,c_2427,c_2425,c_2423,c_2421,c_2419,c_2417,c_2415,
% 1.72/0.99                 c_2413,c_2399,c_2393,c_2382,c_426,c_109,c_105,c_101,
% 1.72/0.99                 c_97,c_93,c_89,c_85,c_81,c_78,c_77,c_76,c_75,c_74,c_73,
% 1.72/0.99                 c_72,c_71,c_70,c_69,c_68,c_67,c_66,c_65,c_64]) ).
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  ------                               Statistics
% 1.72/0.99  
% 1.72/0.99  ------ General
% 1.72/0.99  
% 1.72/0.99  abstr_ref_over_cycles:                  0
% 1.72/0.99  abstr_ref_under_cycles:                 0
% 1.72/0.99  gc_basic_clause_elim:                   0
% 1.72/0.99  forced_gc_time:                         0
% 1.72/0.99  parsing_time:                           0.013
% 1.72/0.99  unif_index_cands_time:                  0.
% 1.72/0.99  unif_index_add_time:                    0.
% 1.72/0.99  orderings_time:                         0.
% 1.72/0.99  out_proof_time:                         0.018
% 1.72/0.99  total_time:                             0.115
% 1.72/0.99  num_of_symbols:                         55
% 1.72/0.99  num_of_terms:                           1403
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing
% 1.72/0.99  
% 1.72/0.99  num_of_splits:                          0
% 1.72/0.99  num_of_split_atoms:                     0
% 1.72/0.99  num_of_reused_defs:                     0
% 1.72/0.99  num_eq_ax_congr_red:                    0
% 1.72/0.99  num_of_sem_filtered_clauses:            0
% 1.72/0.99  num_of_subtypes:                        5
% 1.72/0.99  monotx_restored_types:                  0
% 1.72/0.99  sat_num_of_epr_types:                   0
% 1.72/0.99  sat_num_of_non_cyclic_types:            0
% 1.72/0.99  sat_guarded_non_collapsed_types:        0
% 1.72/0.99  num_pure_diseq_elim:                    0
% 1.72/0.99  simp_replaced_by:                       0
% 1.72/0.99  res_preprocessed:                       79
% 1.72/0.99  prep_upred:                             0
% 1.72/0.99  prep_unflattend:                        0
% 1.72/0.99  smt_new_axioms:                         0
% 1.72/0.99  pred_elim_cands:                        11
% 1.72/0.99  pred_elim:                              1
% 1.72/0.99  pred_elim_cl:                           1
% 1.72/0.99  pred_elim_cycles:                       5
% 1.72/0.99  merged_defs:                            0
% 1.72/0.99  merged_defs_ncl:                        0
% 1.72/0.99  bin_hyper_res:                          0
% 1.72/0.99  prep_cycles:                            2
% 1.72/0.99  pred_elim_time:                         0.024
% 1.72/0.99  splitting_time:                         0.
% 1.72/0.99  sem_filter_time:                        0.
% 1.72/0.99  monotx_time:                            0.
% 1.72/0.99  subtype_inf_time:                       0.
% 1.72/0.99  
% 1.72/0.99  ------ Problem properties
% 1.72/0.99  
% 1.72/0.99  clauses:                                39
% 1.72/0.99  conjectures:                            24
% 1.72/0.99  epr:                                    14
% 1.72/0.99  horn:                                   30
% 1.72/0.99  ground:                                 24
% 1.72/0.99  unary:                                  15
% 1.72/0.99  binary:                                 16
% 1.72/0.99  lits:                                   99
% 1.72/0.99  lits_eq:                                0
% 1.72/0.99  fd_pure:                                0
% 1.72/0.99  fd_pseudo:                              0
% 1.72/0.99  fd_cond:                                0
% 1.72/0.99  fd_pseudo_cond:                         0
% 1.72/0.99  ac_symbols:                             0
% 1.72/0.99  
% 1.72/0.99  ------ Propositional Solver
% 1.72/0.99  
% 1.72/0.99  prop_solver_calls:                      17
% 1.72/0.99  prop_fast_solver_calls:                 754
% 1.72/0.99  smt_solver_calls:                       0
% 1.72/0.99  smt_fast_solver_calls:                  0
% 1.72/0.99  prop_num_of_clauses:                    392
% 1.72/0.99  prop_preprocess_simplified:             2578
% 1.72/0.99  prop_fo_subsumed:                       27
% 1.72/0.99  prop_solver_time:                       0.
% 1.72/0.99  smt_solver_time:                        0.
% 1.72/0.99  smt_fast_solver_time:                   0.
% 1.72/0.99  prop_fast_solver_time:                  0.
% 1.72/0.99  prop_unsat_core_time:                   0.
% 1.72/0.99  
% 1.72/0.99  ------ QBF
% 1.72/0.99  
% 1.72/0.99  qbf_q_res:                              0
% 1.72/0.99  qbf_num_tautologies:                    0
% 1.72/0.99  qbf_prep_cycles:                        0
% 1.72/0.99  
% 1.72/0.99  ------ BMC1
% 1.72/0.99  
% 1.72/0.99  bmc1_current_bound:                     -1
% 1.72/0.99  bmc1_last_solved_bound:                 -1
% 1.72/0.99  bmc1_unsat_core_size:                   -1
% 1.72/0.99  bmc1_unsat_core_parents_size:           -1
% 1.72/0.99  bmc1_merge_next_fun:                    0
% 1.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation
% 1.72/0.99  
% 1.72/0.99  inst_num_of_clauses:                    91
% 1.72/0.99  inst_num_in_passive:                    0
% 1.72/0.99  inst_num_in_active:                     90
% 1.72/0.99  inst_num_in_unprocessed:                0
% 1.72/0.99  inst_num_of_loops:                      116
% 1.72/0.99  inst_num_of_learning_restarts:          0
% 1.72/0.99  inst_num_moves_active_passive:          19
% 1.72/0.99  inst_lit_activity:                      0
% 1.72/0.99  inst_lit_activity_moves:                0
% 1.72/0.99  inst_num_tautologies:                   0
% 1.72/0.99  inst_num_prop_implied:                  0
% 1.72/0.99  inst_num_existing_simplified:           0
% 1.72/0.99  inst_num_eq_res_simplified:             0
% 1.72/0.99  inst_num_child_elim:                    0
% 1.72/0.99  inst_num_of_dismatching_blockings:      2
% 1.72/0.99  inst_num_of_non_proper_insts:           29
% 1.72/0.99  inst_num_of_duplicates:                 0
% 1.72/0.99  inst_inst_num_from_inst_to_res:         0
% 1.72/0.99  inst_dismatching_checking_time:         0.
% 1.72/0.99  
% 1.72/0.99  ------ Resolution
% 1.72/0.99  
% 1.72/0.99  res_num_of_clauses:                     0
% 1.72/0.99  res_num_in_passive:                     0
% 1.72/0.99  res_num_in_active:                      0
% 1.72/0.99  res_num_of_loops:                       81
% 1.72/0.99  res_forward_subset_subsumed:            4
% 1.72/0.99  res_backward_subset_subsumed:           0
% 1.72/0.99  res_forward_subsumed:                   0
% 1.72/0.99  res_backward_subsumed:                  0
% 1.72/0.99  res_forward_subsumption_resolution:     0
% 1.72/0.99  res_backward_subsumption_resolution:    0
% 1.72/0.99  res_clause_to_clause_subsumption:       0
% 1.72/0.99  res_orphan_elimination:                 0
% 1.72/0.99  res_tautology_del:                      30
% 1.72/0.99  res_num_eq_res_simplified:              0
% 1.72/0.99  res_num_sel_changes:                    0
% 1.72/0.99  res_moves_from_active_to_pass:          0
% 1.72/0.99  
% 1.72/0.99  ------ Superposition
% 1.72/0.99  
% 1.72/0.99  sup_time_total:                         0.
% 1.72/0.99  sup_time_generating:                    0.
% 1.72/0.99  sup_time_sim_full:                      0.
% 1.72/0.99  sup_time_sim_immed:                     0.
% 1.72/0.99  
% 1.72/0.99  sup_num_of_clauses:                     0
% 1.72/0.99  sup_num_in_active:                      0
% 1.72/0.99  sup_num_in_passive:                     0
% 1.72/0.99  sup_num_of_loops:                       0
% 1.72/0.99  sup_fw_superposition:                   0
% 1.72/0.99  sup_bw_superposition:                   0
% 1.72/0.99  sup_immediate_simplified:               0
% 1.72/0.99  sup_given_eliminated:                   0
% 1.72/0.99  comparisons_done:                       0
% 1.72/0.99  comparisons_avoided:                    0
% 1.72/0.99  
% 1.72/0.99  ------ Simplifications
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  sim_fw_subset_subsumed:                 0
% 1.72/0.99  sim_bw_subset_subsumed:                 0
% 1.72/0.99  sim_fw_subsumed:                        0
% 1.72/0.99  sim_bw_subsumed:                        0
% 1.72/0.99  sim_fw_subsumption_res:                 0
% 1.72/0.99  sim_bw_subsumption_res:                 0
% 1.72/0.99  sim_tautology_del:                      0
% 1.72/0.99  sim_eq_tautology_del:                   0
% 1.72/0.99  sim_eq_res_simp:                        0
% 1.72/0.99  sim_fw_demodulated:                     0
% 1.72/0.99  sim_bw_demodulated:                     0
% 1.72/0.99  sim_light_normalised:                   0
% 1.72/0.99  sim_joinable_taut:                      0
% 1.72/0.99  sim_joinable_simp:                      0
% 1.72/0.99  sim_ac_normalised:                      0
% 1.72/0.99  sim_smt_subsumption:                    0
% 1.72/0.99  
%------------------------------------------------------------------------------
