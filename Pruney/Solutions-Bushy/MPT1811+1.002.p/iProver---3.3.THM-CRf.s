%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1811+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:31 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
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
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
          & v1_borsuk_1(X3,X0)
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
        & v1_borsuk_1(sK5,X0)
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
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0)
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
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_borsuk_1(sK4,X0)
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_borsuk_1(X2,X0)
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_borsuk_1(X2,sK2)
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
    & v1_borsuk_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_borsuk_1(sK4,sK2)
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
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    v1_borsuk_1(sK4,sK2) ),
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
    | ~ v1_borsuk_1(X2,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_620,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_borsuk_1(X1,X0)
    | ~ v1_borsuk_1(X3,X0)
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
    | ~ v1_borsuk_1(X1_50,X0_50)
    | ~ v1_borsuk_1(X2_50,X0_50)
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
    | ~ v1_borsuk_1(X0_50,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
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
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
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
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
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
    | v1_borsuk_1(sK5,sK2) != iProver_top
    | v1_borsuk_1(sK4,sK2) != iProver_top
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
    ( v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_74,plain,
    ( v1_borsuk_1(sK5,sK2) = iProver_top ),
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
    ( v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_71,plain,
    ( v1_borsuk_1(sK4,sK2) = iProver_top ),
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
