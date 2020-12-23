%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1815+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:32 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  278 ( 932 expanded)
%              Number of clauses        :  187 ( 202 expanded)
%              Number of leaves         :   10 ( 311 expanded)
%              Depth                    :   12
%              Number of atoms          : 1492 (28635 expanded)
%              Number of equality atoms :  163 ( 163 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   78 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
            & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
            & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
            & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
          | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f15])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( sP0(X1,X3,X4,X0,X2)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f18])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                      ( sP1(X2,X0,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
      ( sP1(X2,X0,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
          ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
          & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
            | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
          & m1_pre_topc(X4,X0)
          & v1_tsep_1(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK6))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_tsep_1(X0,X3,sK6),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6))) )
        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6))
            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
          | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_tsep_1(X0,X3,sK6),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6))) ) )
        & m1_pre_topc(sK6,X0)
        & v1_tsep_1(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
              & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                  & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
              & m1_pre_topc(X4,X0)
              & v1_tsep_1(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_tsep_1(X0,sK5,X4),X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4))) )
            & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) )
              | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_tsep_1(X0,sK5,X4),X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4))) ) )
            & m1_pre_topc(X4,X0)
            & v1_tsep_1(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK5,X0)
        & v1_tsep_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                  & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                      & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                    | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                  & m1_pre_topc(X4,X0)
                  & v1_tsep_1(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & v1_tsep_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,X4))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4))) )
                & ( ( m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4))
                    & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) )
                  | ( m1_subset_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4))) ) )
                & m1_pre_topc(X4,X0)
                & v1_tsep_1(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4))) )
                    & ( ( m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4))
                        & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) )
                      | ( m1_subset_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4))) ) )
                    & m1_pre_topc(X4,X0)
                    & v1_tsep_1(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
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
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                        & m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))) ) )
                      & m1_pre_topc(X4,sK2)
                      & v1_tsep_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ) )
    & m1_pre_topc(sK6,sK2)
    & v1_tsep_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26,f25,f24,f23,f22])).

fof(f91,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
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
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
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

cnf(c_1,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2557,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | v5_pre_topc(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_tsep_1(X1_50,X0_50,X2_50),X3_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2915,plain,
    ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_tsep_1(sK2,sK5,X0_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_2557])).

cnf(c_4070,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(instantiation,[status(thm)],[c_2915])).

cnf(c_4071,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4070])).

cnf(c_2,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2556,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | v1_funct_2(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2916,plain,
    ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50)) ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_3917,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2916])).

cnf(c_3918,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3917])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2550,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2999,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_3527,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_3551,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3527])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2552,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2997,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_3528,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2997])).

cnf(c_3549,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3528])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2551,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3000,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_50,X0_50) ),
    inference(instantiation,[status(thm)],[c_2551])).

cnf(c_3529,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_3547,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3529])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2549,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3003,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,X0_50,X0_51,X1_50)) ),
    inference(instantiation,[status(thm)],[c_2549])).

cnf(c_3530,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_3545,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3530])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2546,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3002,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,X0_50,X0_51,sK5),u1_struct_0(sK5),u1_struct_0(X0_50)) ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_3531,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_3543,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3531])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2547,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3001,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,X0_50,X0_51,sK5),sK5,X0_50) ),
    inference(instantiation,[status(thm)],[c_2547])).

cnf(c_3532,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_3541,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3532])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2548,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2998,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,X0_50,X0_51,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_50)))) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_3533,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_3539,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3533])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2545,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3004,plain,
    ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,X0_50,X0_51,sK5)) ),
    inference(instantiation,[status(thm)],[c_2545])).

cnf(c_3534,plain,
    ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_3537,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3534])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2553,plain,
    ( sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50))
    | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50)
    | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50)
    | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
    | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50))))
    | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50))
    | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2942,plain,
    ( sP0(sK3,X0_50,sK4,sK2,X1_50)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1_50),u1_struct_0(X1_50),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X1_50),X1_50,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X1_50)) ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_3217,plain,
    ( sP0(sK3,sK6,sK4,sK2,X0_50)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_3526,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_3535,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3526])).

cnf(c_3403,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_3415,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3403])).

cnf(c_3404,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_3413,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3404])).

cnf(c_3405,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_3411,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3405])).

cnf(c_3406,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_3409,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3406])).

cnf(c_3198,plain,
    ( sP0(sK3,sK5,sK4,sK2,X0_50)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_3398,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK5)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3198])).

cnf(c_3407,plain,
    ( sP0(sK3,sK5,sK4,sK2,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3398])).

cnf(c_0,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2558,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | m1_subset_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50)))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2914,plain,
    ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50)))) ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_3272,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_2914])).

cnf(c_3279,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3272])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
    | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
    | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2554,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | ~ v1_funct_2(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50))
    | ~ v5_pre_topc(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_tsep_1(X1_50,X0_50,X2_50),X3_50)
    | ~ m1_subset_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50))))
    | ~ v1_funct_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2913,plain,
    ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | sP0(X1_50,X0_50,X0_51,sK2,sK5)
    | ~ v1_funct_2(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50))
    | ~ v5_pre_topc(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_tsep_1(sK2,sK5,X0_50),X1_50)
    | ~ m1_subset_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50))))
    | ~ v1_funct_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50))) ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_3273,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_2913])).

cnf(c_3277,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2555,plain,
    ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
    | v1_funct_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2917,plain,
    ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50))) ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_3274,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ sP0(sK3,sK6,sK4,sK2,sK5)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_3275,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
    | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3274])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
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

cnf(c_640,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_tsep_1(X3,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

cnf(c_2496,plain,
    ( sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(X3_50))
    | ~ v1_tsep_1(X0_50,X1_50)
    | ~ v1_tsep_1(X2_50,X1_50)
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X1_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X3_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_640])).

cnf(c_2838,plain,
    ( sP1(sK5,sK2,X0_51,X0_50,X1_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X1_50))
    | ~ v1_tsep_1(X0_50,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50))))
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_2496])).

cnf(c_3050,plain,
    ( sP1(sK5,sK2,X0_51,sK6,X0_50)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50))))
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_3186,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_3187,plain,
    ( sP1(sK5,sK2,sK4,sK6,sK3) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK5,sK2) != iProver_top
    | v1_tsep_1(sK6,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_16,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_111,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_110,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_109,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_108,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_107,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_106,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_105,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_104,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_103,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_102,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_101,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_100,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_99,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_98,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_97,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_96,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_95,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_94,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_93,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_92,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_91,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_90,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_89,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_88,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_40,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_87,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_86,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_85,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_84,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_83,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_82,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_46,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_81,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_80,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_79,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_49,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_78,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_50,negated_conjecture,
    ( v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_77,plain,
    ( v1_tsep_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_51,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_76,plain,
    ( v2_struct_0(sK6) != iProver_top ),
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
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_72,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_56,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_71,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_57,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_70,plain,
    ( v1_funct_1(sK4) = iProver_top ),
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
    inference(minisat,[status(thm)],[c_4071,c_3918,c_3551,c_3549,c_3547,c_3545,c_3543,c_3541,c_3539,c_3537,c_3535,c_3415,c_3413,c_3411,c_3409,c_3407,c_3279,c_3277,c_3275,c_3187,c_111,c_110,c_109,c_108,c_107,c_106,c_105,c_104,c_103,c_102,c_101,c_100,c_99,c_98,c_97,c_96,c_95,c_94,c_93,c_92,c_91,c_90,c_89,c_88,c_87,c_86,c_85,c_84,c_83,c_82,c_81,c_80,c_79,c_78,c_77,c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68,c_67,c_66,c_65,c_64])).


%------------------------------------------------------------------------------
