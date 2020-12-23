%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:18 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
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
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_borsuk_1(X4,X0)
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
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
          & v1_borsuk_1(X4,X0)
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
        & v1_borsuk_1(sK6,X0)
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
              & v1_borsuk_1(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
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
            & v1_borsuk_1(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK5,X0)
        & v1_borsuk_1(sK5,X0)
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
                  & v1_borsuk_1(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
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
                & v1_borsuk_1(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
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
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                    & v1_borsuk_1(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
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
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
                      & v1_borsuk_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_borsuk_1(X3,sK2)
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
    & v1_borsuk_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_borsuk_1(sK5,sK2)
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
    v1_borsuk_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
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
    | ~ v1_borsuk_1(X2,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_640,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_borsuk_1(X3,X1)
    | ~ v1_borsuk_1(X0,X1)
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
    | ~ v1_borsuk_1(X0_50,X1_50)
    | ~ v1_borsuk_1(X2_50,X1_50)
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
    | ~ v1_borsuk_1(X0_50,sK2)
    | ~ v1_borsuk_1(sK5,sK2)
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
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK6,sK2)
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
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK6,sK2)
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
    | v1_borsuk_1(sK5,sK2) != iProver_top
    | v1_borsuk_1(sK6,sK2) != iProver_top
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
    ( v1_borsuk_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_77,plain,
    ( v1_borsuk_1(sK6,sK2) = iProver_top ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:11:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.95/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.95/0.98  
% 1.95/0.98  ------  iProver source info
% 1.95/0.98  
% 1.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.95/0.98  git: non_committed_changes: false
% 1.95/0.98  git: last_make_outside_of_git: false
% 1.95/0.98  
% 1.95/0.98  ------ 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options
% 1.95/0.98  
% 1.95/0.98  --out_options                           all
% 1.95/0.98  --tptp_safe_out                         true
% 1.95/0.98  --problem_path                          ""
% 1.95/0.98  --include_path                          ""
% 1.95/0.98  --clausifier                            res/vclausify_rel
% 1.95/0.98  --clausifier_options                    --mode clausify
% 1.95/0.98  --stdin                                 false
% 1.95/0.98  --stats_out                             all
% 1.95/0.98  
% 1.95/0.98  ------ General Options
% 1.95/0.98  
% 1.95/0.98  --fof                                   false
% 1.95/0.98  --time_out_real                         305.
% 1.95/0.98  --time_out_virtual                      -1.
% 1.95/0.98  --symbol_type_check                     false
% 1.95/0.98  --clausify_out                          false
% 1.95/0.98  --sig_cnt_out                           false
% 1.95/0.98  --trig_cnt_out                          false
% 1.95/0.98  --trig_cnt_out_tolerance                1.
% 1.95/0.98  --trig_cnt_out_sk_spl                   false
% 1.95/0.98  --abstr_cl_out                          false
% 1.95/0.98  
% 1.95/0.98  ------ Global Options
% 1.95/0.98  
% 1.95/0.98  --schedule                              default
% 1.95/0.98  --add_important_lit                     false
% 1.95/0.98  --prop_solver_per_cl                    1000
% 1.95/0.98  --min_unsat_core                        false
% 1.95/0.98  --soft_assumptions                      false
% 1.95/0.98  --soft_lemma_size                       3
% 1.95/0.98  --prop_impl_unit_size                   0
% 1.95/0.98  --prop_impl_unit                        []
% 1.95/0.98  --share_sel_clauses                     true
% 1.95/0.98  --reset_solvers                         false
% 1.95/0.98  --bc_imp_inh                            [conj_cone]
% 1.95/0.98  --conj_cone_tolerance                   3.
% 1.95/0.98  --extra_neg_conj                        none
% 1.95/0.98  --large_theory_mode                     true
% 1.95/0.98  --prolific_symb_bound                   200
% 1.95/0.98  --lt_threshold                          2000
% 1.95/0.98  --clause_weak_htbl                      true
% 1.95/0.98  --gc_record_bc_elim                     false
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing Options
% 1.95/0.98  
% 1.95/0.98  --preprocessing_flag                    true
% 1.95/0.98  --time_out_prep_mult                    0.1
% 1.95/0.98  --splitting_mode                        input
% 1.95/0.98  --splitting_grd                         true
% 1.95/0.98  --splitting_cvd                         false
% 1.95/0.98  --splitting_cvd_svl                     false
% 1.95/0.98  --splitting_nvd                         32
% 1.95/0.98  --sub_typing                            true
% 1.95/0.98  --prep_gs_sim                           true
% 1.95/0.98  --prep_unflatten                        true
% 1.95/0.98  --prep_res_sim                          true
% 1.95/0.98  --prep_upred                            true
% 1.95/0.98  --prep_sem_filter                       exhaustive
% 1.95/0.98  --prep_sem_filter_out                   false
% 1.95/0.98  --pred_elim                             true
% 1.95/0.98  --res_sim_input                         true
% 1.95/0.98  --eq_ax_congr_red                       true
% 1.95/0.98  --pure_diseq_elim                       true
% 1.95/0.98  --brand_transform                       false
% 1.95/0.98  --non_eq_to_eq                          false
% 1.95/0.98  --prep_def_merge                        true
% 1.95/0.98  --prep_def_merge_prop_impl              false
% 1.95/0.98  --prep_def_merge_mbd                    true
% 1.95/0.98  --prep_def_merge_tr_red                 false
% 1.95/0.98  --prep_def_merge_tr_cl                  false
% 1.95/0.98  --smt_preprocessing                     true
% 1.95/0.98  --smt_ac_axioms                         fast
% 1.95/0.98  --preprocessed_out                      false
% 1.95/0.98  --preprocessed_stats                    false
% 1.95/0.98  
% 1.95/0.98  ------ Abstraction refinement Options
% 1.95/0.98  
% 1.95/0.98  --abstr_ref                             []
% 1.95/0.98  --abstr_ref_prep                        false
% 1.95/0.98  --abstr_ref_until_sat                   false
% 1.95/0.98  --abstr_ref_sig_restrict                funpre
% 1.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/0.98  --abstr_ref_under                       []
% 1.95/0.98  
% 1.95/0.98  ------ SAT Options
% 1.95/0.98  
% 1.95/0.98  --sat_mode                              false
% 1.95/0.98  --sat_fm_restart_options                ""
% 1.95/0.98  --sat_gr_def                            false
% 1.95/0.98  --sat_epr_types                         true
% 1.95/0.98  --sat_non_cyclic_types                  false
% 1.95/0.98  --sat_finite_models                     false
% 1.95/0.98  --sat_fm_lemmas                         false
% 1.95/0.98  --sat_fm_prep                           false
% 1.95/0.98  --sat_fm_uc_incr                        true
% 1.95/0.98  --sat_out_model                         small
% 1.95/0.98  --sat_out_clauses                       false
% 1.95/0.98  
% 1.95/0.98  ------ QBF Options
% 1.95/0.98  
% 1.95/0.98  --qbf_mode                              false
% 1.95/0.98  --qbf_elim_univ                         false
% 1.95/0.98  --qbf_dom_inst                          none
% 1.95/0.98  --qbf_dom_pre_inst                      false
% 1.95/0.98  --qbf_sk_in                             false
% 1.95/0.98  --qbf_pred_elim                         true
% 1.95/0.98  --qbf_split                             512
% 1.95/0.98  
% 1.95/0.98  ------ BMC1 Options
% 1.95/0.98  
% 1.95/0.98  --bmc1_incremental                      false
% 1.95/0.98  --bmc1_axioms                           reachable_all
% 1.95/0.98  --bmc1_min_bound                        0
% 1.95/0.98  --bmc1_max_bound                        -1
% 1.95/0.98  --bmc1_max_bound_default                -1
% 1.95/0.98  --bmc1_symbol_reachability              true
% 1.95/0.98  --bmc1_property_lemmas                  false
% 1.95/0.98  --bmc1_k_induction                      false
% 1.95/0.98  --bmc1_non_equiv_states                 false
% 1.95/0.98  --bmc1_deadlock                         false
% 1.95/0.98  --bmc1_ucm                              false
% 1.95/0.98  --bmc1_add_unsat_core                   none
% 1.95/0.98  --bmc1_unsat_core_children              false
% 1.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/0.98  --bmc1_out_stat                         full
% 1.95/0.98  --bmc1_ground_init                      false
% 1.95/0.98  --bmc1_pre_inst_next_state              false
% 1.95/0.98  --bmc1_pre_inst_state                   false
% 1.95/0.98  --bmc1_pre_inst_reach_state             false
% 1.95/0.98  --bmc1_out_unsat_core                   false
% 1.95/0.98  --bmc1_aig_witness_out                  false
% 1.95/0.98  --bmc1_verbose                          false
% 1.95/0.98  --bmc1_dump_clauses_tptp                false
% 1.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.95/0.98  --bmc1_dump_file                        -
% 1.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.95/0.98  --bmc1_ucm_extend_mode                  1
% 1.95/0.98  --bmc1_ucm_init_mode                    2
% 1.95/0.98  --bmc1_ucm_cone_mode                    none
% 1.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.95/0.98  --bmc1_ucm_relax_model                  4
% 1.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/0.98  --bmc1_ucm_layered_model                none
% 1.95/0.98  --bmc1_ucm_max_lemma_size               10
% 1.95/0.98  
% 1.95/0.98  ------ AIG Options
% 1.95/0.98  
% 1.95/0.98  --aig_mode                              false
% 1.95/0.98  
% 1.95/0.98  ------ Instantiation Options
% 1.95/0.98  
% 1.95/0.98  --instantiation_flag                    true
% 1.95/0.98  --inst_sos_flag                         false
% 1.95/0.98  --inst_sos_phase                        true
% 1.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel_side                     num_symb
% 1.95/0.98  --inst_solver_per_active                1400
% 1.95/0.98  --inst_solver_calls_frac                1.
% 1.95/0.98  --inst_passive_queue_type               priority_queues
% 1.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/0.98  --inst_passive_queues_freq              [25;2]
% 1.95/0.98  --inst_dismatching                      true
% 1.95/0.98  --inst_eager_unprocessed_to_passive     true
% 1.95/0.98  --inst_prop_sim_given                   true
% 1.95/0.98  --inst_prop_sim_new                     false
% 1.95/0.98  --inst_subs_new                         false
% 1.95/0.98  --inst_eq_res_simp                      false
% 1.95/0.98  --inst_subs_given                       false
% 1.95/0.98  --inst_orphan_elimination               true
% 1.95/0.98  --inst_learning_loop_flag               true
% 1.95/0.98  --inst_learning_start                   3000
% 1.95/0.98  --inst_learning_factor                  2
% 1.95/0.98  --inst_start_prop_sim_after_learn       3
% 1.95/0.98  --inst_sel_renew                        solver
% 1.95/0.98  --inst_lit_activity_flag                true
% 1.95/0.98  --inst_restr_to_given                   false
% 1.95/0.98  --inst_activity_threshold               500
% 1.95/0.98  --inst_out_proof                        true
% 1.95/0.98  
% 1.95/0.98  ------ Resolution Options
% 1.95/0.98  
% 1.95/0.98  --resolution_flag                       true
% 1.95/0.98  --res_lit_sel                           adaptive
% 1.95/0.98  --res_lit_sel_side                      none
% 1.95/0.98  --res_ordering                          kbo
% 1.95/0.98  --res_to_prop_solver                    active
% 1.95/0.98  --res_prop_simpl_new                    false
% 1.95/0.98  --res_prop_simpl_given                  true
% 1.95/0.98  --res_passive_queue_type                priority_queues
% 1.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/0.98  --res_passive_queues_freq               [15;5]
% 1.95/0.98  --res_forward_subs                      full
% 1.95/0.98  --res_backward_subs                     full
% 1.95/0.98  --res_forward_subs_resolution           true
% 1.95/0.98  --res_backward_subs_resolution          true
% 1.95/0.98  --res_orphan_elimination                true
% 1.95/0.98  --res_time_limit                        2.
% 1.95/0.98  --res_out_proof                         true
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Options
% 1.95/0.98  
% 1.95/0.98  --superposition_flag                    true
% 1.95/0.98  --sup_passive_queue_type                priority_queues
% 1.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.95/0.98  --demod_completeness_check              fast
% 1.95/0.98  --demod_use_ground                      true
% 1.95/0.98  --sup_to_prop_solver                    passive
% 1.95/0.98  --sup_prop_simpl_new                    true
% 1.95/0.98  --sup_prop_simpl_given                  true
% 1.95/0.98  --sup_fun_splitting                     false
% 1.95/0.98  --sup_smt_interval                      50000
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Simplification Setup
% 1.95/0.98  
% 1.95/0.98  --sup_indices_passive                   []
% 1.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_full_bw                           [BwDemod]
% 1.95/0.98  --sup_immed_triv                        [TrivRules]
% 1.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_immed_bw_main                     []
% 1.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  
% 1.95/0.98  ------ Combination Options
% 1.95/0.98  
% 1.95/0.98  --comb_res_mult                         3
% 1.95/0.98  --comb_sup_mult                         2
% 1.95/0.98  --comb_inst_mult                        10
% 1.95/0.98  
% 1.95/0.98  ------ Debug Options
% 1.95/0.98  
% 1.95/0.98  --dbg_backtrace                         false
% 1.95/0.98  --dbg_dump_prop_clauses                 false
% 1.95/0.98  --dbg_dump_prop_clauses_file            -
% 1.95/0.98  --dbg_out_stat                          false
% 1.95/0.98  ------ Parsing...
% 1.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.95/0.98  ------ Proving...
% 1.95/0.98  ------ Problem Properties 
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  clauses                                 63
% 1.95/0.98  conjectures                             48
% 1.95/0.98  EPR                                     13
% 1.95/0.98  Horn                                    30
% 1.95/0.98  unary                                   15
% 1.95/0.98  binary                                  40
% 1.95/0.98  lits                                    150
% 1.95/0.98  lits eq                                 0
% 1.95/0.98  fd_pure                                 0
% 1.95/0.98  fd_pseudo                               0
% 1.95/0.98  fd_cond                                 0
% 1.95/0.98  fd_pseudo_cond                          0
% 1.95/0.98  AC symbols                              0
% 1.95/0.98  
% 1.95/0.98  ------ Schedule dynamic 5 is on 
% 1.95/0.98  
% 1.95/0.98  ------ no equalities: superposition off 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  ------ 
% 1.95/0.98  Current options:
% 1.95/0.98  ------ 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options
% 1.95/0.98  
% 1.95/0.98  --out_options                           all
% 1.95/0.98  --tptp_safe_out                         true
% 1.95/0.98  --problem_path                          ""
% 1.95/0.98  --include_path                          ""
% 1.95/0.98  --clausifier                            res/vclausify_rel
% 1.95/0.98  --clausifier_options                    --mode clausify
% 1.95/0.98  --stdin                                 false
% 1.95/0.98  --stats_out                             all
% 1.95/0.98  
% 1.95/0.98  ------ General Options
% 1.95/0.98  
% 1.95/0.98  --fof                                   false
% 1.95/0.98  --time_out_real                         305.
% 1.95/0.98  --time_out_virtual                      -1.
% 1.95/0.98  --symbol_type_check                     false
% 1.95/0.98  --clausify_out                          false
% 1.95/0.98  --sig_cnt_out                           false
% 1.95/0.98  --trig_cnt_out                          false
% 1.95/0.98  --trig_cnt_out_tolerance                1.
% 1.95/0.98  --trig_cnt_out_sk_spl                   false
% 1.95/0.98  --abstr_cl_out                          false
% 1.95/0.98  
% 1.95/0.98  ------ Global Options
% 1.95/0.98  
% 1.95/0.98  --schedule                              default
% 1.95/0.98  --add_important_lit                     false
% 1.95/0.98  --prop_solver_per_cl                    1000
% 1.95/0.98  --min_unsat_core                        false
% 1.95/0.98  --soft_assumptions                      false
% 1.95/0.98  --soft_lemma_size                       3
% 1.95/0.98  --prop_impl_unit_size                   0
% 1.95/0.98  --prop_impl_unit                        []
% 1.95/0.98  --share_sel_clauses                     true
% 1.95/0.98  --reset_solvers                         false
% 1.95/0.98  --bc_imp_inh                            [conj_cone]
% 1.95/0.98  --conj_cone_tolerance                   3.
% 1.95/0.98  --extra_neg_conj                        none
% 1.95/0.98  --large_theory_mode                     true
% 1.95/0.98  --prolific_symb_bound                   200
% 1.95/0.98  --lt_threshold                          2000
% 1.95/0.98  --clause_weak_htbl                      true
% 1.95/0.98  --gc_record_bc_elim                     false
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing Options
% 1.95/0.98  
% 1.95/0.98  --preprocessing_flag                    true
% 1.95/0.98  --time_out_prep_mult                    0.1
% 1.95/0.98  --splitting_mode                        input
% 1.95/0.98  --splitting_grd                         true
% 1.95/0.98  --splitting_cvd                         false
% 1.95/0.98  --splitting_cvd_svl                     false
% 1.95/0.98  --splitting_nvd                         32
% 1.95/0.98  --sub_typing                            true
% 1.95/0.98  --prep_gs_sim                           true
% 1.95/0.98  --prep_unflatten                        true
% 1.95/0.98  --prep_res_sim                          true
% 1.95/0.98  --prep_upred                            true
% 1.95/0.98  --prep_sem_filter                       exhaustive
% 1.95/0.98  --prep_sem_filter_out                   false
% 1.95/0.98  --pred_elim                             true
% 1.95/0.98  --res_sim_input                         true
% 1.95/0.98  --eq_ax_congr_red                       true
% 1.95/0.98  --pure_diseq_elim                       true
% 1.95/0.98  --brand_transform                       false
% 1.95/0.98  --non_eq_to_eq                          false
% 1.95/0.98  --prep_def_merge                        true
% 1.95/0.98  --prep_def_merge_prop_impl              false
% 1.95/0.98  --prep_def_merge_mbd                    true
% 1.95/0.98  --prep_def_merge_tr_red                 false
% 1.95/0.98  --prep_def_merge_tr_cl                  false
% 1.95/0.98  --smt_preprocessing                     true
% 1.95/0.98  --smt_ac_axioms                         fast
% 1.95/0.98  --preprocessed_out                      false
% 1.95/0.98  --preprocessed_stats                    false
% 1.95/0.98  
% 1.95/0.98  ------ Abstraction refinement Options
% 1.95/0.98  
% 1.95/0.98  --abstr_ref                             []
% 1.95/0.98  --abstr_ref_prep                        false
% 1.95/0.98  --abstr_ref_until_sat                   false
% 1.95/0.98  --abstr_ref_sig_restrict                funpre
% 1.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/0.98  --abstr_ref_under                       []
% 1.95/0.98  
% 1.95/0.98  ------ SAT Options
% 1.95/0.98  
% 1.95/0.98  --sat_mode                              false
% 1.95/0.98  --sat_fm_restart_options                ""
% 1.95/0.98  --sat_gr_def                            false
% 1.95/0.98  --sat_epr_types                         true
% 1.95/0.98  --sat_non_cyclic_types                  false
% 1.95/0.98  --sat_finite_models                     false
% 1.95/0.98  --sat_fm_lemmas                         false
% 1.95/0.98  --sat_fm_prep                           false
% 1.95/0.98  --sat_fm_uc_incr                        true
% 1.95/0.98  --sat_out_model                         small
% 1.95/0.98  --sat_out_clauses                       false
% 1.95/0.98  
% 1.95/0.98  ------ QBF Options
% 1.95/0.98  
% 1.95/0.98  --qbf_mode                              false
% 1.95/0.98  --qbf_elim_univ                         false
% 1.95/0.98  --qbf_dom_inst                          none
% 1.95/0.98  --qbf_dom_pre_inst                      false
% 1.95/0.98  --qbf_sk_in                             false
% 1.95/0.98  --qbf_pred_elim                         true
% 1.95/0.98  --qbf_split                             512
% 1.95/0.98  
% 1.95/0.98  ------ BMC1 Options
% 1.95/0.98  
% 1.95/0.98  --bmc1_incremental                      false
% 1.95/0.98  --bmc1_axioms                           reachable_all
% 1.95/0.98  --bmc1_min_bound                        0
% 1.95/0.98  --bmc1_max_bound                        -1
% 1.95/0.98  --bmc1_max_bound_default                -1
% 1.95/0.98  --bmc1_symbol_reachability              true
% 1.95/0.98  --bmc1_property_lemmas                  false
% 1.95/0.98  --bmc1_k_induction                      false
% 1.95/0.98  --bmc1_non_equiv_states                 false
% 1.95/0.98  --bmc1_deadlock                         false
% 1.95/0.98  --bmc1_ucm                              false
% 1.95/0.98  --bmc1_add_unsat_core                   none
% 1.95/0.98  --bmc1_unsat_core_children              false
% 1.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/0.98  --bmc1_out_stat                         full
% 1.95/0.98  --bmc1_ground_init                      false
% 1.95/0.98  --bmc1_pre_inst_next_state              false
% 1.95/0.98  --bmc1_pre_inst_state                   false
% 1.95/0.98  --bmc1_pre_inst_reach_state             false
% 1.95/0.98  --bmc1_out_unsat_core                   false
% 1.95/0.98  --bmc1_aig_witness_out                  false
% 1.95/0.98  --bmc1_verbose                          false
% 1.95/0.98  --bmc1_dump_clauses_tptp                false
% 1.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.95/0.98  --bmc1_dump_file                        -
% 1.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.95/0.98  --bmc1_ucm_extend_mode                  1
% 1.95/0.98  --bmc1_ucm_init_mode                    2
% 1.95/0.98  --bmc1_ucm_cone_mode                    none
% 1.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.95/0.98  --bmc1_ucm_relax_model                  4
% 1.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/0.98  --bmc1_ucm_layered_model                none
% 1.95/0.98  --bmc1_ucm_max_lemma_size               10
% 1.95/0.98  
% 1.95/0.98  ------ AIG Options
% 1.95/0.98  
% 1.95/0.98  --aig_mode                              false
% 1.95/0.98  
% 1.95/0.98  ------ Instantiation Options
% 1.95/0.98  
% 1.95/0.98  --instantiation_flag                    true
% 1.95/0.98  --inst_sos_flag                         false
% 1.95/0.98  --inst_sos_phase                        true
% 1.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel_side                     none
% 1.95/0.98  --inst_solver_per_active                1400
% 1.95/0.98  --inst_solver_calls_frac                1.
% 1.95/0.98  --inst_passive_queue_type               priority_queues
% 1.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/0.98  --inst_passive_queues_freq              [25;2]
% 1.95/0.98  --inst_dismatching                      true
% 1.95/0.98  --inst_eager_unprocessed_to_passive     true
% 1.95/0.98  --inst_prop_sim_given                   true
% 1.95/0.98  --inst_prop_sim_new                     false
% 1.95/0.98  --inst_subs_new                         false
% 1.95/0.98  --inst_eq_res_simp                      false
% 1.95/0.98  --inst_subs_given                       false
% 1.95/0.98  --inst_orphan_elimination               true
% 1.95/0.98  --inst_learning_loop_flag               true
% 1.95/0.98  --inst_learning_start                   3000
% 1.95/0.98  --inst_learning_factor                  2
% 1.95/0.98  --inst_start_prop_sim_after_learn       3
% 1.95/0.98  --inst_sel_renew                        solver
% 1.95/0.98  --inst_lit_activity_flag                true
% 1.95/0.98  --inst_restr_to_given                   false
% 1.95/0.98  --inst_activity_threshold               500
% 1.95/0.98  --inst_out_proof                        true
% 1.95/0.98  
% 1.95/0.98  ------ Resolution Options
% 1.95/0.98  
% 1.95/0.98  --resolution_flag                       false
% 1.95/0.98  --res_lit_sel                           adaptive
% 1.95/0.98  --res_lit_sel_side                      none
% 1.95/0.98  --res_ordering                          kbo
% 1.95/0.98  --res_to_prop_solver                    active
% 1.95/0.98  --res_prop_simpl_new                    false
% 1.95/0.98  --res_prop_simpl_given                  true
% 1.95/0.98  --res_passive_queue_type                priority_queues
% 1.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/0.98  --res_passive_queues_freq               [15;5]
% 1.95/0.98  --res_forward_subs                      full
% 1.95/0.98  --res_backward_subs                     full
% 1.95/0.98  --res_forward_subs_resolution           true
% 1.95/0.98  --res_backward_subs_resolution          true
% 1.95/0.98  --res_orphan_elimination                true
% 1.95/0.98  --res_time_limit                        2.
% 1.95/0.98  --res_out_proof                         true
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Options
% 1.95/0.98  
% 1.95/0.98  --superposition_flag                    false
% 1.95/0.98  --sup_passive_queue_type                priority_queues
% 1.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.95/0.98  --demod_completeness_check              fast
% 1.95/0.98  --demod_use_ground                      true
% 1.95/0.98  --sup_to_prop_solver                    passive
% 1.95/0.98  --sup_prop_simpl_new                    true
% 1.95/0.98  --sup_prop_simpl_given                  true
% 1.95/0.98  --sup_fun_splitting                     false
% 1.95/0.98  --sup_smt_interval                      50000
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Simplification Setup
% 1.95/0.98  
% 1.95/0.98  --sup_indices_passive                   []
% 1.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_full_bw                           [BwDemod]
% 1.95/0.98  --sup_immed_triv                        [TrivRules]
% 1.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_immed_bw_main                     []
% 1.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  
% 1.95/0.98  ------ Combination Options
% 1.95/0.98  
% 1.95/0.98  --comb_res_mult                         3
% 1.95/0.98  --comb_sup_mult                         2
% 1.95/0.98  --comb_inst_mult                        10
% 1.95/0.98  
% 1.95/0.98  ------ Debug Options
% 1.95/0.98  
% 1.95/0.98  --dbg_backtrace                         false
% 1.95/0.98  --dbg_dump_prop_clauses                 false
% 1.95/0.98  --dbg_dump_prop_clauses_file            -
% 1.95/0.98  --dbg_out_stat                          false
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  ------ Proving...
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  % SZS status Theorem for theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  fof(f12,plain,(
% 1.95/0.98    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 1.95/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.95/0.98  
% 1.95/0.98  fof(f14,plain,(
% 1.95/0.98    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.95/0.98    inference(nnf_transformation,[],[f12])).
% 1.95/0.98  
% 1.95/0.98  fof(f15,plain,(
% 1.95/0.98    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.95/0.98    inference(flattening,[],[f14])).
% 1.95/0.98  
% 1.95/0.98  fof(f16,plain,(
% 1.95/0.98    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 1.95/0.98    inference(rectify,[],[f15])).
% 1.95/0.98  
% 1.95/0.98  fof(f31,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f16])).
% 1.95/0.98  
% 1.95/0.98  fof(f30,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f16])).
% 1.95/0.98  
% 1.95/0.98  fof(f11,plain,(
% 1.95/0.98    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 1.95/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.95/0.98  
% 1.95/0.98  fof(f17,plain,(
% 1.95/0.98    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.95/0.98    inference(nnf_transformation,[],[f11])).
% 1.95/0.98  
% 1.95/0.98  fof(f18,plain,(
% 1.95/0.98    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.95/0.98    inference(flattening,[],[f17])).
% 1.95/0.98  
% 1.95/0.98  fof(f19,plain,(
% 1.95/0.98    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.95/0.98    inference(rectify,[],[f18])).
% 1.95/0.98  
% 1.95/0.98  fof(f38,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f40,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f39,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f37,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f34,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f35,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f36,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f33,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f41,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f32,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f16])).
% 1.95/0.98  
% 1.95/0.98  fof(f28,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f16])).
% 1.95/0.98  
% 1.95/0.98  fof(f29,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f16])).
% 1.95/0.98  
% 1.95/0.98  fof(f1,axiom,(
% 1.95/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f5,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f1])).
% 1.95/0.98  
% 1.95/0.98  fof(f6,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f5])).
% 1.95/0.98  
% 1.95/0.98  fof(f13,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.95/0.98    inference(definition_folding,[],[f6,f12,f11])).
% 1.95/0.98  
% 1.95/0.98  fof(f42,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f13])).
% 1.95/0.98  
% 1.95/0.98  fof(f2,axiom,(
% 1.95/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f7,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f2])).
% 1.95/0.98  
% 1.95/0.98  fof(f8,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f7])).
% 1.95/0.98  
% 1.95/0.98  fof(f43,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f8])).
% 1.95/0.98  
% 1.95/0.98  fof(f3,conjecture,(
% 1.95/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))))))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f4,negated_conjecture,(
% 1.95/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))))))))),
% 1.95/0.98    inference(negated_conjecture,[],[f3])).
% 1.95/0.98  
% 1.95/0.98  fof(f9,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f4])).
% 1.95/0.98  
% 1.95/0.98  fof(f10,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f9])).
% 1.95/0.98  
% 1.95/0.98  fof(f20,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.95/0.98    inference(nnf_transformation,[],[f10])).
% 1.95/0.98  
% 1.95/0.98  fof(f21,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f20])).
% 1.95/0.98  
% 1.95/0.98  fof(f26,plain,(
% 1.95/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_tsep_1(X0,X3,sK6),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK6),sK6,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK6),u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK6)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),k1_tsep_1(X0,X3,sK6),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6)),u1_struct_0(k1_tsep_1(X0,X3,sK6)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,sK6))))) & m1_pre_topc(sK6,X0) & v1_borsuk_1(sK6,X0) & ~v2_struct_0(sK6))) )),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f25,plain,(
% 1.95/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_tsep_1(X0,sK5,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK5),sK5,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,sK5))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),k1_tsep_1(X0,sK5,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4)),u1_struct_0(k1_tsep_1(X0,sK5,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,sK5,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,X0) & v1_borsuk_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f24,plain,(
% 1.95/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X4)) & m1_subset_1(k2_tmap_1(X0,X1,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,sK4,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f23,plain,(
% 1.95/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),sK3) | ~v1_funct_2(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),sK3) & v1_funct_2(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(X0,sK3,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f22,plain,(
% 1.95/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))))) & m1_pre_topc(X4,X0) & v1_borsuk_1(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)))) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))))) & m1_pre_topc(X4,sK2) & v1_borsuk_1(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f27,plain,(
% 1.95/0.99    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))))) & m1_pre_topc(sK6,sK2) & v1_borsuk_1(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & v1_borsuk_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26,f25,f24,f23,f22])).
% 1.95/0.99  
% 1.95/0.99  fof(f91,plain,(
% 1.95/0.99    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f90,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f89,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f88,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f87,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f86,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f85,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f84,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f83,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f82,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f81,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f80,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f79,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f78,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f77,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f76,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f75,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f74,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f73,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f72,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f71,plain,(
% 1.95/0.99    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f70,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f69,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f68,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f67,plain,(
% 1.95/0.99    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f66,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f65,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f64,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f63,plain,(
% 1.95/0.99    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f62,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f61,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f60,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f59,plain,(
% 1.95/0.99    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f58,plain,(
% 1.95/0.99    m1_pre_topc(sK6,sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f57,plain,(
% 1.95/0.99    v1_borsuk_1(sK6,sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f56,plain,(
% 1.95/0.99    ~v2_struct_0(sK6)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f55,plain,(
% 1.95/0.99    m1_pre_topc(sK5,sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f54,plain,(
% 1.95/0.99    v1_borsuk_1(sK5,sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f53,plain,(
% 1.95/0.99    ~v2_struct_0(sK5)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f52,plain,(
% 1.95/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f51,plain,(
% 1.95/0.99    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f50,plain,(
% 1.95/0.99    v1_funct_1(sK4)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f49,plain,(
% 1.95/0.99    l1_pre_topc(sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f48,plain,(
% 1.95/0.99    v2_pre_topc(sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f47,plain,(
% 1.95/0.99    ~v2_struct_0(sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f46,plain,(
% 1.95/0.99    l1_pre_topc(sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f45,plain,(
% 1.95/0.99    v2_pre_topc(sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f44,plain,(
% 1.95/0.99    ~v2_struct_0(sK2)),
% 1.95/0.99    inference(cnf_transformation,[],[f27])).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1,plain,
% 1.95/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ),
% 1.95/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2557,plain,
% 1.95/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_tsep_1(X1_50,X0_50,X2_50),X3_50) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2915,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 1.95/0.99      | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_tsep_1(sK2,sK5,X0_50),X1_50) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2557]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_4070,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 1.95/0.99      | ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2915]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_4071,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 1.95/0.99      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_4070]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2,plain,
% 1.95/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2556,plain,
% 1.95/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2916,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 1.95/0.99      | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2556]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3917,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 1.95/0.99      | ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2916]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3918,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 1.95/0.99      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3917]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_8,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2550,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2999,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2550]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3527,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2999]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3551,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3527]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_6,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2552,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2997,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2552]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3528,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2997]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3549,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3528]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_7,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2551,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3000,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_50,X0_50) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2551]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3529,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3000]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3547,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3529]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_9,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2549,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3003,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,X0_50,X0_51,X1_50)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2549]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3530,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3003]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3545,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3530]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_12,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2546,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3002,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,X0_50,X0_51,sK5),u1_struct_0(sK5),u1_struct_0(X0_50)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2546]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3531,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3002]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3543,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3531]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_11,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2547,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3001,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,X0_50,X0_51,sK5),sK5,X0_50) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2547]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3532,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3001]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3541,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3532]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_10,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2548,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50)))) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2998,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,X0_50,X0_51,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_50)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2548]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3533,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2998]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3539,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3533]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_13,plain,
% 1.95/0.99      ( ~ sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2545,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3004,plain,
% 1.95/0.99      ( ~ sP0(X0_50,X1_50,X0_51,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,X0_50,X0_51,sK5)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2545]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3534,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3004]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3537,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3534]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_5,plain,
% 1.95/0.99      ( sP0(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2553,plain,
% 1.95/0.99      ( sP0(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),u1_struct_0(X3_50),u1_struct_0(X0_50))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),X1_50,X0_50)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),X3_50,X0_50)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X0_50))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X1_50))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(X2_50,X0_50,X0_51,X3_50)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2942,plain,
% 1.95/0.99      ( sP0(sK3,X0_50,sK4,sK2,X1_50)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1_50),u1_struct_0(X1_50),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X1_50),X1_50,sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X1_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X1_50)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2553]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3217,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,X0_50)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2942]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3526,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3217]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3535,plain,
% 1.95/0.99      ( sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3526]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3403,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3002]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3415,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3403]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3404,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3001]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3413,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3404]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3405,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2998]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3411,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3405]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3406,plain,
% 1.95/0.99      ( ~ sP0(sK3,sK5,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3004]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3409,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3406]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3198,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,X0_50)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0_50),u1_struct_0(X0_50),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0_50),X0_50,sK3)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK3))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0_50))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2942]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3398,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,sK5)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3198]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3407,plain,
% 1.95/0.99      ( sP0(sK3,sK5,sK4,sK2,sK5) = iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3398]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_0,plain,
% 1.95/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2558,plain,
% 1.95/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50)))) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2914,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 1.95/0.99      | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2558]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3272,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 1.95/0.99      | ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2914]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3279,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 1.95/0.99      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3272]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_4,plain,
% 1.95/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | sP0(X4,X3,X2,X1,X0)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2554,plain,
% 1.95/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_tsep_1(X1_50,X0_50,X2_50),X3_50)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_50,X0_50,X2_50)),u1_struct_0(X3_50))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50))) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2913,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 1.95/0.99      | sP0(X1_50,X0_50,X0_51,sK2,sK5)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_tsep_1(sK2,sK5,X0_50),X1_50)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X0_50)),u1_struct_0(X1_50))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2554]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3273,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 1.95/0.99      | sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2913]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3277,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 1.95/0.99      | sP0(sK3,sK6,sK4,sK2,sK5) = iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3273]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3,plain,
% 1.95/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2555,plain,
% 1.95/0.99      ( ~ sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | ~ sP0(X3_50,X2_50,X0_51,X1_50,X0_50)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(X1_50,X3_50,X0_51,k1_tsep_1(X1_50,X0_50,X2_50))) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2917,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 1.95/0.99      | ~ sP0(X1_50,X0_50,X0_51,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,X1_50,X0_51,k1_tsep_1(sK2,sK5,X0_50))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2555]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3274,plain,
% 1.95/0.99      ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
% 1.95/0.99      | ~ sP0(sK3,sK6,sK4,sK2,sK5)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2917]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3275,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3) != iProver_top
% 1.95/0.99      | sP0(sK3,sK6,sK4,sK2,sK5) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3274]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_14,plain,
% 1.95/0.99      ( sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ r4_tsep_1(X1,X0,X3)
% 1.95/0.99      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 1.95/0.99      | ~ m1_pre_topc(X3,X1)
% 1.95/0.99      | ~ m1_pre_topc(X0,X1)
% 1.95/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 1.95/0.99      | ~ v2_pre_topc(X4)
% 1.95/0.99      | ~ v2_pre_topc(X1)
% 1.95/0.99      | ~ l1_pre_topc(X4)
% 1.95/0.99      | ~ l1_pre_topc(X1)
% 1.95/0.99      | v2_struct_0(X1)
% 1.95/0.99      | v2_struct_0(X4)
% 1.95/0.99      | v2_struct_0(X0)
% 1.95/0.99      | v2_struct_0(X3)
% 1.95/0.99      | ~ v1_funct_1(X2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_15,plain,
% 1.95/0.99      ( r4_tsep_1(X0,X1,X2)
% 1.95/0.99      | ~ v1_borsuk_1(X2,X0)
% 1.95/0.99      | ~ v1_borsuk_1(X1,X0)
% 1.95/0.99      | ~ m1_pre_topc(X2,X0)
% 1.95/0.99      | ~ m1_pre_topc(X1,X0)
% 1.95/0.99      | ~ v2_pre_topc(X0)
% 1.95/0.99      | ~ l1_pre_topc(X0)
% 1.95/0.99      | v2_struct_0(X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_640,plain,
% 1.95/0.99      ( sP1(X0,X1,X2,X3,X4)
% 1.95/0.99      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
% 1.95/0.99      | ~ v1_borsuk_1(X3,X1)
% 1.95/0.99      | ~ v1_borsuk_1(X0,X1)
% 1.95/0.99      | ~ m1_pre_topc(X3,X1)
% 1.95/0.99      | ~ m1_pre_topc(X0,X1)
% 1.95/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 1.95/0.99      | ~ v2_pre_topc(X4)
% 1.95/0.99      | ~ v2_pre_topc(X1)
% 1.95/0.99      | ~ l1_pre_topc(X4)
% 1.95/0.99      | ~ l1_pre_topc(X1)
% 1.95/0.99      | v2_struct_0(X3)
% 1.95/0.99      | v2_struct_0(X0)
% 1.95/0.99      | v2_struct_0(X4)
% 1.95/0.99      | v2_struct_0(X1)
% 1.95/0.99      | ~ v1_funct_1(X2) ),
% 1.95/0.99      inference(resolution,[status(thm)],[c_14,c_15]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2496,plain,
% 1.95/0.99      ( sP1(X0_50,X1_50,X0_51,X2_50,X3_50)
% 1.95/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(X3_50))
% 1.95/0.99      | ~ v1_borsuk_1(X0_50,X1_50)
% 1.95/0.99      | ~ v1_borsuk_1(X2_50,X1_50)
% 1.95/0.99      | ~ m1_pre_topc(X0_50,X1_50)
% 1.95/0.99      | ~ m1_pre_topc(X2_50,X1_50)
% 1.95/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X3_50))))
% 1.95/0.99      | ~ v2_pre_topc(X1_50)
% 1.95/0.99      | ~ v2_pre_topc(X3_50)
% 1.95/0.99      | ~ l1_pre_topc(X1_50)
% 1.95/0.99      | ~ l1_pre_topc(X3_50)
% 1.95/0.99      | v2_struct_0(X3_50)
% 1.95/0.99      | v2_struct_0(X0_50)
% 1.95/0.99      | v2_struct_0(X1_50)
% 1.95/0.99      | v2_struct_0(X2_50)
% 1.95/0.99      | ~ v1_funct_1(X0_51) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_640]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2838,plain,
% 1.95/0.99      ( sP1(sK5,sK2,X0_51,X0_50,X1_50)
% 1.95/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X1_50))
% 1.95/0.99      | ~ v1_borsuk_1(X0_50,sK2)
% 1.95/0.99      | ~ v1_borsuk_1(sK5,sK2)
% 1.95/0.99      | ~ m1_pre_topc(X0_50,sK2)
% 1.95/0.99      | ~ m1_pre_topc(sK5,sK2)
% 1.95/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50))))
% 1.95/0.99      | ~ v2_pre_topc(X1_50)
% 1.95/0.99      | ~ v2_pre_topc(sK2)
% 1.95/0.99      | ~ l1_pre_topc(X1_50)
% 1.95/0.99      | ~ l1_pre_topc(sK2)
% 1.95/0.99      | v2_struct_0(X0_50)
% 1.95/0.99      | v2_struct_0(X1_50)
% 1.95/0.99      | v2_struct_0(sK5)
% 1.95/0.99      | v2_struct_0(sK2)
% 1.95/0.99      | ~ v1_funct_1(X0_51) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2496]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3050,plain,
% 1.95/0.99      ( sP1(sK5,sK2,X0_51,sK6,X0_50)
% 1.95/0.99      | ~ v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50))
% 1.95/0.99      | ~ v1_borsuk_1(sK5,sK2)
% 1.95/0.99      | ~ v1_borsuk_1(sK6,sK2)
% 1.95/0.99      | ~ m1_pre_topc(sK5,sK2)
% 1.95/0.99      | ~ m1_pre_topc(sK6,sK2)
% 1.95/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50))))
% 1.95/0.99      | ~ v2_pre_topc(X0_50)
% 1.95/0.99      | ~ v2_pre_topc(sK2)
% 1.95/0.99      | ~ l1_pre_topc(X0_50)
% 1.95/0.99      | ~ l1_pre_topc(sK2)
% 1.95/0.99      | v2_struct_0(X0_50)
% 1.95/0.99      | v2_struct_0(sK5)
% 1.95/0.99      | v2_struct_0(sK6)
% 1.95/0.99      | v2_struct_0(sK2)
% 1.95/0.99      | ~ v1_funct_1(X0_51) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2838]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3186,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3)
% 1.95/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_borsuk_1(sK5,sK2)
% 1.95/0.99      | ~ v1_borsuk_1(sK6,sK2)
% 1.95/0.99      | ~ m1_pre_topc(sK5,sK2)
% 1.95/0.99      | ~ m1_pre_topc(sK6,sK2)
% 1.95/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v2_pre_topc(sK3)
% 1.95/0.99      | ~ v2_pre_topc(sK2)
% 1.95/0.99      | ~ l1_pre_topc(sK3)
% 1.95/0.99      | ~ l1_pre_topc(sK2)
% 1.95/0.99      | v2_struct_0(sK5)
% 1.95/0.99      | v2_struct_0(sK6)
% 1.95/0.99      | v2_struct_0(sK3)
% 1.95/0.99      | v2_struct_0(sK2)
% 1.95/0.99      | ~ v1_funct_1(sK4) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3050]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3187,plain,
% 1.95/0.99      ( sP1(sK5,sK2,sK4,sK6,sK3) = iProver_top
% 1.95/0.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v1_borsuk_1(sK5,sK2) != iProver_top
% 1.95/0.99      | v1_borsuk_1(sK6,sK2) != iProver_top
% 1.95/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 1.95/0.99      | m1_pre_topc(sK6,sK2) != iProver_top
% 1.95/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | v2_pre_topc(sK3) != iProver_top
% 1.95/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.95/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.95/0.99      | l1_pre_topc(sK2) != iProver_top
% 1.95/0.99      | v2_struct_0(sK5) = iProver_top
% 1.95/0.99      | v2_struct_0(sK6) = iProver_top
% 1.95/0.99      | v2_struct_0(sK3) = iProver_top
% 1.95/0.99      | v2_struct_0(sK2) = iProver_top
% 1.95/0.99      | v1_funct_1(sK4) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3186]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_16,negated_conjecture,
% 1.95/0.99      ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 1.95/0.99      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.95/0.99      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
% 1.95/0.99      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f91]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_111,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) != iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) != iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_17,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f90]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_110,plain,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_18,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f89]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_109,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_19,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f88]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_108,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_20,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f87]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_107,plain,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_21,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f86]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_106,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_22,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f85]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_105,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_23,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_104,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_24,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f83]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_103,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_25,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_102,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_26,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_101,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_27,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_100,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_28,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_99,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_29,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_98,plain,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_30,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_97,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_31,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_96,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_32,negated_conjecture,
% 1.95/0.99      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_95,plain,
% 1.95/0.99      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_33,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_94,plain,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_34,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_93,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_35,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_92,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_36,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_91,plain,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_37,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_90,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_38,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_89,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_39,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_88,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_40,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_87,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_41,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_86,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_42,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_85,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_43,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_84,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_44,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_83,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_45,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_82,plain,
% 1.95/0.99      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_46,negated_conjecture,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_81,plain,
% 1.95/0.99      ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_47,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_80,plain,
% 1.95/0.99      ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_48,negated_conjecture,
% 1.95/0.99      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_79,plain,
% 1.95/0.99      ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) = iProver_top
% 1.95/0.99      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_49,negated_conjecture,
% 1.95/0.99      ( m1_pre_topc(sK6,sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_78,plain,
% 1.95/0.99      ( m1_pre_topc(sK6,sK2) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_50,negated_conjecture,
% 1.95/0.99      ( v1_borsuk_1(sK6,sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_77,plain,
% 1.95/0.99      ( v1_borsuk_1(sK6,sK2) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_51,negated_conjecture,
% 1.95/0.99      ( ~ v2_struct_0(sK6) ),
% 1.95/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_76,plain,
% 1.95/0.99      ( v2_struct_0(sK6) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_52,negated_conjecture,
% 1.95/0.99      ( m1_pre_topc(sK5,sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_75,plain,
% 1.95/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_53,negated_conjecture,
% 1.95/0.99      ( v1_borsuk_1(sK5,sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_74,plain,
% 1.95/0.99      ( v1_borsuk_1(sK5,sK2) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_54,negated_conjecture,
% 1.95/0.99      ( ~ v2_struct_0(sK5) ),
% 1.95/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_73,plain,
% 1.95/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_55,negated_conjecture,
% 1.95/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_72,plain,
% 1.95/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_56,negated_conjecture,
% 1.95/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_71,plain,
% 1.95/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_57,negated_conjecture,
% 1.95/0.99      ( v1_funct_1(sK4) ),
% 1.95/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_70,plain,
% 1.95/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_58,negated_conjecture,
% 1.95/0.99      ( l1_pre_topc(sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_69,plain,
% 1.95/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_59,negated_conjecture,
% 1.95/0.99      ( v2_pre_topc(sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_68,plain,
% 1.95/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_60,negated_conjecture,
% 1.95/0.99      ( ~ v2_struct_0(sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_67,plain,
% 1.95/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_61,negated_conjecture,
% 1.95/0.99      ( l1_pre_topc(sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_66,plain,
% 1.95/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_62,negated_conjecture,
% 1.95/0.99      ( v2_pre_topc(sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_65,plain,
% 1.95/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_63,negated_conjecture,
% 1.95/0.99      ( ~ v2_struct_0(sK2) ),
% 1.95/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_64,plain,
% 1.95/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(contradiction,plain,
% 1.95/0.99      ( $false ),
% 1.95/0.99      inference(minisat,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_4071,c_3918,c_3551,c_3549,c_3547,c_3545,c_3543,c_3541,
% 1.95/0.99                 c_3539,c_3537,c_3535,c_3415,c_3413,c_3411,c_3409,c_3407,
% 1.95/0.99                 c_3279,c_3277,c_3275,c_3187,c_111,c_110,c_109,c_108,
% 1.95/0.99                 c_107,c_106,c_105,c_104,c_103,c_102,c_101,c_100,c_99,
% 1.95/0.99                 c_98,c_97,c_96,c_95,c_94,c_93,c_92,c_91,c_90,c_89,c_88,
% 1.95/0.99                 c_87,c_86,c_85,c_84,c_83,c_82,c_81,c_80,c_79,c_78,c_77,
% 1.95/0.99                 c_76,c_75,c_74,c_73,c_72,c_71,c_70,c_69,c_68,c_67,c_66,
% 1.95/0.99                 c_65,c_64]) ).
% 1.95/0.99  
% 1.95/0.99  
% 1.95/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.95/0.99  
% 1.95/0.99  ------                               Statistics
% 1.95/0.99  
% 1.95/0.99  ------ General
% 1.95/0.99  
% 1.95/0.99  abstr_ref_over_cycles:                  0
% 1.95/0.99  abstr_ref_under_cycles:                 0
% 1.95/0.99  gc_basic_clause_elim:                   0
% 1.95/0.99  forced_gc_time:                         0
% 1.95/0.99  parsing_time:                           0.027
% 1.95/0.99  unif_index_cands_time:                  0.
% 1.95/0.99  unif_index_add_time:                    0.
% 1.95/0.99  orderings_time:                         0.
% 1.95/0.99  out_proof_time:                         0.02
% 1.95/0.99  total_time:                             0.164
% 1.95/0.99  num_of_symbols:                         55
% 1.95/0.99  num_of_terms:                           1775
% 1.95/0.99  
% 1.95/0.99  ------ Preprocessing
% 1.95/0.99  
% 1.95/0.99  num_of_splits:                          0
% 1.95/0.99  num_of_split_atoms:                     0
% 1.95/0.99  num_of_reused_defs:                     0
% 1.95/0.99  num_eq_ax_congr_red:                    0
% 1.95/0.99  num_of_sem_filtered_clauses:            0
% 1.95/0.99  num_of_subtypes:                        5
% 1.95/0.99  monotx_restored_types:                  0
% 1.95/0.99  sat_num_of_epr_types:                   0
% 1.95/0.99  sat_num_of_non_cyclic_types:            0
% 1.95/0.99  sat_guarded_non_collapsed_types:        0
% 1.95/0.99  num_pure_diseq_elim:                    0
% 1.95/0.99  simp_replaced_by:                       0
% 1.95/0.99  res_preprocessed:                       127
% 1.95/0.99  prep_upred:                             0
% 1.95/0.99  prep_unflattend:                        0
% 1.95/0.99  smt_new_axioms:                         0
% 1.95/0.99  pred_elim_cands:                        11
% 1.95/0.99  pred_elim:                              1
% 1.95/0.99  pred_elim_cl:                           1
% 1.95/0.99  pred_elim_cycles:                       5
% 1.95/0.99  merged_defs:                            0
% 1.95/0.99  merged_defs_ncl:                        0
% 1.95/0.99  bin_hyper_res:                          0
% 1.95/0.99  prep_cycles:                            2
% 1.95/0.99  pred_elim_time:                         0.037
% 1.95/0.99  splitting_time:                         0.
% 1.95/0.99  sem_filter_time:                        0.
% 1.95/0.99  monotx_time:                            0.
% 1.95/0.99  subtype_inf_time:                       0.001
% 1.95/0.99  
% 1.95/0.99  ------ Problem properties
% 1.95/0.99  
% 1.95/0.99  clauses:                                63
% 1.95/0.99  conjectures:                            48
% 1.95/0.99  epr:                                    13
% 1.95/0.99  horn:                                   30
% 1.95/0.99  ground:                                 48
% 1.95/0.99  unary:                                  15
% 1.95/0.99  binary:                                 40
% 1.95/0.99  lits:                                   150
% 1.95/0.99  lits_eq:                                0
% 1.95/0.99  fd_pure:                                0
% 1.95/0.99  fd_pseudo:                              0
% 1.95/0.99  fd_cond:                                0
% 1.95/0.99  fd_pseudo_cond:                         0
% 1.95/0.99  ac_symbols:                             0
% 1.95/0.99  
% 1.95/0.99  ------ Propositional Solver
% 1.95/0.99  
% 1.95/0.99  prop_solver_calls:                      16
% 1.95/0.99  prop_fast_solver_calls:                 982
% 1.95/0.99  smt_solver_calls:                       0
% 1.95/0.99  smt_fast_solver_calls:                  0
% 1.95/0.99  prop_num_of_clauses:                    917
% 1.95/0.99  prop_preprocess_simplified:             3828
% 1.95/0.99  prop_fo_subsumed:                       0
% 1.95/0.99  prop_solver_time:                       0.
% 1.95/0.99  smt_solver_time:                        0.
% 1.95/0.99  smt_fast_solver_time:                   0.
% 1.95/0.99  prop_fast_solver_time:                  0.
% 1.95/0.99  prop_unsat_core_time:                   0.
% 1.95/0.99  
% 1.95/0.99  ------ QBF
% 1.95/0.99  
% 1.95/0.99  qbf_q_res:                              0
% 1.95/0.99  qbf_num_tautologies:                    0
% 1.95/0.99  qbf_prep_cycles:                        0
% 1.95/0.99  
% 1.95/0.99  ------ BMC1
% 1.95/0.99  
% 1.95/0.99  bmc1_current_bound:                     -1
% 1.95/0.99  bmc1_last_solved_bound:                 -1
% 1.95/0.99  bmc1_unsat_core_size:                   -1
% 1.95/0.99  bmc1_unsat_core_parents_size:           -1
% 1.95/0.99  bmc1_merge_next_fun:                    0
% 1.95/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.95/0.99  
% 1.95/0.99  ------ Instantiation
% 1.95/0.99  
% 1.95/0.99  inst_num_of_clauses:                    262
% 1.95/0.99  inst_num_in_passive:                    29
% 1.95/0.99  inst_num_in_active:                     228
% 1.95/0.99  inst_num_in_unprocessed:                4
% 1.95/0.99  inst_num_of_loops:                      303
% 1.95/0.99  inst_num_of_learning_restarts:          0
% 1.95/0.99  inst_num_moves_active_passive:          68
% 1.95/0.99  inst_lit_activity:                      0
% 1.95/0.99  inst_lit_activity_moves:                0
% 1.95/0.99  inst_num_tautologies:                   0
% 1.95/0.99  inst_num_prop_implied:                  0
% 1.95/0.99  inst_num_existing_simplified:           0
% 1.95/0.99  inst_num_eq_res_simplified:             0
% 1.95/0.99  inst_num_child_elim:                    0
% 1.95/0.99  inst_num_of_dismatching_blockings:      73
% 1.95/0.99  inst_num_of_non_proper_insts:           164
% 1.95/0.99  inst_num_of_duplicates:                 0
% 1.95/0.99  inst_inst_num_from_inst_to_res:         0
% 1.95/0.99  inst_dismatching_checking_time:         0.
% 1.95/0.99  
% 1.95/0.99  ------ Resolution
% 1.95/0.99  
% 1.95/0.99  res_num_of_clauses:                     0
% 1.95/0.99  res_num_in_passive:                     0
% 1.95/0.99  res_num_in_active:                      0
% 1.95/0.99  res_num_of_loops:                       129
% 1.95/0.99  res_forward_subset_subsumed:            0
% 1.95/0.99  res_backward_subset_subsumed:           0
% 1.95/0.99  res_forward_subsumed:                   0
% 1.95/0.99  res_backward_subsumed:                  0
% 1.95/0.99  res_forward_subsumption_resolution:     0
% 1.95/0.99  res_backward_subsumption_resolution:    0
% 1.95/0.99  res_clause_to_clause_subsumption:       292
% 1.95/0.99  res_orphan_elimination:                 0
% 1.95/0.99  res_tautology_del:                      24
% 1.95/0.99  res_num_eq_res_simplified:              0
% 1.95/0.99  res_num_sel_changes:                    0
% 1.95/0.99  res_moves_from_active_to_pass:          0
% 1.95/0.99  
% 1.95/0.99  ------ Superposition
% 1.95/0.99  
% 1.95/0.99  sup_time_total:                         0.
% 1.95/0.99  sup_time_generating:                    0.
% 1.95/0.99  sup_time_sim_full:                      0.
% 1.95/0.99  sup_time_sim_immed:                     0.
% 1.95/0.99  
% 1.95/0.99  sup_num_of_clauses:                     0
% 1.95/0.99  sup_num_in_active:                      0
% 1.95/0.99  sup_num_in_passive:                     0
% 1.95/0.99  sup_num_of_loops:                       0
% 1.95/0.99  sup_fw_superposition:                   0
% 1.95/0.99  sup_bw_superposition:                   0
% 1.95/0.99  sup_immediate_simplified:               0
% 1.95/0.99  sup_given_eliminated:                   0
% 1.95/0.99  comparisons_done:                       0
% 1.95/0.99  comparisons_avoided:                    0
% 1.95/0.99  
% 1.95/0.99  ------ Simplifications
% 1.95/0.99  
% 1.95/0.99  
% 1.95/0.99  sim_fw_subset_subsumed:                 0
% 1.95/0.99  sim_bw_subset_subsumed:                 0
% 1.95/0.99  sim_fw_subsumed:                        0
% 1.95/0.99  sim_bw_subsumed:                        0
% 1.95/0.99  sim_fw_subsumption_res:                 0
% 1.95/0.99  sim_bw_subsumption_res:                 0
% 1.95/0.99  sim_tautology_del:                      0
% 1.95/0.99  sim_eq_tautology_del:                   0
% 1.95/0.99  sim_eq_res_simp:                        0
% 1.95/0.99  sim_fw_demodulated:                     0
% 1.95/0.99  sim_bw_demodulated:                     0
% 1.95/0.99  sim_light_normalised:                   0
% 1.95/0.99  sim_joinable_taut:                      0
% 1.95/0.99  sim_joinable_simp:                      0
% 1.95/0.99  sim_ac_normalised:                      0
% 1.95/0.99  sim_smt_subsumption:                    0
% 1.95/0.99  
%------------------------------------------------------------------------------
