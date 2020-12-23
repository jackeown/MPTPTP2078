%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  227 (32991 expanded)
%              Number of leaves         :   16 (11380 expanded)
%              Depth                    :   49
%              Number of atoms          :  951 (204348 expanded)
%              Number of equality atoms :  164 (7833 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(subsumption_resolution,[],[f383,f120])).

fof(f120,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(resolution,[],[f116,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v2_funct_1(X2)
        | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
      & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v2_funct_1(X2)
        | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
      & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        & v5_pre_topc(X2,X0,X1)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
        & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f116,plain,(
    sP0(sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f50,plain,(
    v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    & v3_tops_2(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                & v3_tops_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2)
              & v3_tops_2(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2)
            & v3_tops_2(X2,sK2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2)
          & v3_tops_2(X2,sK2,sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2)
        & v3_tops_2(X2,sK2,sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
      & v3_tops_2(sK4,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                 => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

fof(f115,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | sP0(sK2,sK3,sK4) ),
    inference(resolution,[],[f113,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_tops_2(X0,X2,X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( v3_tops_2(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v3_tops_2(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( ( v3_tops_2(X2,X0,X1)
          | ~ sP0(X0,X1,X2) )
        & ( sP0(X0,X1,X2)
          | ~ v3_tops_2(X2,X0,X1) ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ( v3_tops_2(X2,X0,X1)
      <=> sP0(X0,X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f113,plain,(
    sP1(sK4,sK3,sK2) ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,
    ( ~ v1_funct_1(sK4)
    | sP1(sK4,sK3,sK2) ),
    inference(subsumption_resolution,[],[f111,f86])).

fof(f86,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f81,f80])).

fof(f80,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f52,f78])).

fof(f78,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f81,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f48,f79])).

fof(f79,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | sP1(sK4,sK3,sK2) ),
    inference(resolution,[],[f110,f85])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f82,f80])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f49,f79])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ v1_funct_1(X1)
      | sP1(X1,sK3,sK2) ) ),
    inference(forward_demodulation,[],[f109,f80])).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),u1_struct_0(sK3))
      | sP1(X1,sK3,sK2) ) ),
    inference(forward_demodulation,[],[f106,f80])).

fof(f106,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),u1_struct_0(sK3))
      | sP1(X1,sK3,sK2) ) ),
    inference(resolution,[],[f102,f46])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | sP1(X0,X1,sK2) ) ),
    inference(forward_demodulation,[],[f101,f79])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | sP1(X0,X1,sK2) ) ),
    inference(forward_demodulation,[],[f99,f79])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | sP1(X0,X1,sK2) ) ),
    inference(resolution,[],[f65,f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f33,f32])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(f383,plain,(
    ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(backward_demodulation,[],[f288,f374])).

fof(f374,plain,(
    sK4 = k2_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f373,f274])).

fof(f274,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(backward_demodulation,[],[f150,f273])).

fof(f273,plain,(
    k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f272,f87])).

fof(f87,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f69,f85])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f272,plain,
    ( k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f271,f47])).

fof(f271,plain,
    ( k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f270,f121])).

fof(f121,plain,(
    v2_funct_1(sK4) ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f270,plain,
    ( k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f269,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f269,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f268,f135])).

fof(f135,plain,(
    v1_funct_1(k2_funct_1(sK4)) ),
    inference(backward_demodulation,[],[f90,f133])).

fof(f133,plain,(
    k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f132,f47])).

fof(f132,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f131,f86])).

fof(f131,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f130,f85])).

fof(f130,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f129,f121])).

fof(f129,plain,
    ( ~ v2_funct_1(sK4)
    | k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v2_funct_1(sK4)
    | k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f73,f125])).

fof(f125,plain,(
    k2_struct_0(sK3) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f124,f79])).

fof(f124,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f118,f80])).

fof(f118,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(resolution,[],[f116,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f90,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f89,f47])).

fof(f89,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f88,f86])).

fof(f88,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f70,f85])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f268,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f267,f149])).

fof(f149,plain,(
    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f148,f47])).

fof(f148,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f147,f86])).

fof(f147,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f146,f85])).

fof(f146,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f71,f133])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f267,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f262,f136])).

fof(f136,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f93,f133])).

fof(f93,plain,(
    m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f92,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f91,f86])).

fof(f91,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f72,f85])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f262,plain,
    ( ~ v2_funct_1(k2_funct_1(sK4))
    | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( k2_struct_0(sK2) != k2_struct_0(sK2)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(superposition,[],[f73,f258])).

fof(f258,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f257,f133])).

fof(f257,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f256,f47])).

fof(f256,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f255,f121])).

fof(f255,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f254,f85])).

fof(f254,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f253,f86])).

fof(f253,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f252])).

fof(f252,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f251,f125])).

fof(f251,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f250,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f250,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f248,f78])).

fof(f248,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f237,f80])).

fof(f237,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(X1),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f236,f79])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(forward_demodulation,[],[f235,f79])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(forward_demodulation,[],[f234,f79])).

fof(f234,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(forward_demodulation,[],[f232,f79])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(resolution,[],[f55,f77])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f150,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f142,f149])).

fof(f142,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f139,f133])).

fof(f139,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))) ),
    inference(backward_demodulation,[],[f98,f133])).

fof(f98,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)))
    | ~ v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f95,f90])).

fof(f95,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)))
    | ~ v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(resolution,[],[f93,f70])).

fof(f373,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f372,f310])).

fof(f310,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f309,f135])).

fof(f309,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f308,f149])).

fof(f308,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f307,f136])).

fof(f307,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(superposition,[],[f71,f273])).

fof(f372,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f371,f275])).

fof(f275,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f151,f273])).

fof(f151,plain,(
    m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f141,f149])).

fof(f141,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f138,f133])).

fof(f138,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f97,f133])).

fof(f97,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f94,f90])).

fof(f94,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(resolution,[],[f93,f72])).

fof(f371,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f370,f47])).

fof(f370,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f369,f86])).

fof(f369,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f368,f85])).

fof(f368,plain,
    ( sK4 = k2_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK4))) ),
    inference(resolution,[],[f367,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f367,plain,(
    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4) ),
    inference(forward_demodulation,[],[f366,f273])).

fof(f366,plain,(
    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK4) ),
    inference(forward_demodulation,[],[f365,f133])).

fof(f365,plain,(
    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) ),
    inference(subsumption_resolution,[],[f364,f47])).

fof(f364,plain,
    ( r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f363,f121])).

fof(f363,plain,
    ( r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f362,f85])).

fof(f362,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f361,f86])).

fof(f361,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f359,f125])).

fof(f359,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)),X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f358,f45])).

fof(f358,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)),X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f356,f78])).

fof(f356,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)),X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f319,f80])).

fof(f319,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | r2_funct_2(k2_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(X1),X0)),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f318,f79])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0) ) ),
    inference(forward_demodulation,[],[f317,f79])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0) ) ),
    inference(forward_demodulation,[],[f316,f79])).

fof(f316,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0) ) ),
    inference(forward_demodulation,[],[f314,f79])).

fof(f314,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0) ) ),
    inference(resolution,[],[f53,f77])).

% (20816)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (20808)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f288,plain,(
    ~ v5_pre_topc(k2_funct_1(k2_funct_1(sK4)),sK2,sK3) ),
    inference(backward_demodulation,[],[f259,f273])).

fof(f259,plain,(
    ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) ),
    inference(subsumption_resolution,[],[f231,f258])).

fof(f231,plain,
    ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f208,f230])).

fof(f230,plain,(
    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f229,f133])).

fof(f229,plain,(
    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f228,f47])).

fof(f228,plain,
    ( k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f227,f121])).

fof(f227,plain,
    ( k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f226,f85])).

fof(f226,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f225,f86])).

fof(f225,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
    | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f223,f125])).

fof(f223,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f222,f45])).

fof(f222,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f220,f78])).

fof(f220,plain,(
    ! [X1] :
      ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))
      | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f214,f80])).

fof(f214,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(X1),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f213,f79])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(forward_demodulation,[],[f212,f79])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1))))
      | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(forward_demodulation,[],[f211,f79])).

fof(f211,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(forward_demodulation,[],[f209,f79])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) ) ),
    inference(resolution,[],[f54,f77])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f208,plain,
    ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f207,f80])).

fof(f207,plain,
    ( k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) ),
    inference(forward_demodulation,[],[f206,f79])).

fof(f206,plain,
    ( k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f205,f80])).

fof(f205,plain,
    ( k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f204,f79])).

fof(f204,plain,
    ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f203,f80])).

fof(f203,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f202,f79])).

fof(f202,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f201,f87])).

fof(f201,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f200,f47])).

fof(f200,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f199,f121])).

fof(f199,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f198,f170])).

fof(f170,plain,(
    ~ sP0(sK3,sK2,k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f168,f134])).

fof(f134,plain,(
    ~ v3_tops_2(k2_funct_1(sK4),sK3,sK2) ),
    inference(backward_demodulation,[],[f84,f133])).

fof(f84,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2) ),
    inference(backward_demodulation,[],[f83,f80])).

fof(f83,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) ),
    inference(backward_demodulation,[],[f51,f79])).

fof(f51,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,
    ( ~ sP0(sK3,sK2,k2_funct_1(sK4))
    | v3_tops_2(k2_funct_1(sK4),sK3,sK2) ),
    inference(resolution,[],[f167,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | v3_tops_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f167,plain,(
    sP1(k2_funct_1(sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f166,f135])).

fof(f166,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | sP1(k2_funct_1(sK4),sK2,sK3) ),
    inference(subsumption_resolution,[],[f165,f149])).

fof(f165,plain,
    ( ~ v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sP1(k2_funct_1(sK4),sK2,sK3) ),
    inference(resolution,[],[f162,f136])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
      | ~ v1_funct_2(X0,k2_struct_0(sK3),k2_struct_0(sK2))
      | ~ v1_funct_1(X0)
      | sP1(X0,sK2,sK3) ) ),
    inference(forward_demodulation,[],[f161,f79])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK3),u1_struct_0(sK2))
      | sP1(X0,sK2,sK3) ) ),
    inference(forward_demodulation,[],[f159,f79])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2))))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK3),u1_struct_0(sK2))
      | sP1(X0,sK2,sK3) ) ),
    inference(resolution,[],[f104,f44])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X3))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X3))
      | sP1(X2,X3,sK3) ) ),
    inference(forward_demodulation,[],[f103,f80])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | sP1(X2,X3,sK3) ) ),
    inference(forward_demodulation,[],[f100,f80])).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | sP1(X2,X3,sK3) ) ),
    inference(resolution,[],[f65,f46])).

fof(f198,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)
    | sP0(sK3,sK2,k2_funct_1(sK4))
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f185,f140])).

fof(f140,plain,(
    v5_pre_topc(k2_funct_1(sK4),sK3,sK2) ),
    inference(backward_demodulation,[],[f123,f133])).

fof(f123,plain,(
    v5_pre_topc(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2) ),
    inference(forward_demodulation,[],[f122,f79])).

fof(f122,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2) ),
    inference(forward_demodulation,[],[f117,f80])).

fof(f117,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) ),
    inference(resolution,[],[f116,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k2_funct_1(X2),X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(X2)),X1,X0)
      | sP0(X0,X1,k2_funct_1(X2))
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(X2))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f64,f68])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | sP0(X0,X1,X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (20797)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (20796)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (20805)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (20795)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (20802)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (20794)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (20815)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (20793)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (20814)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (20810)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (20804)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (20799)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (20806)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (20803)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (20809)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (20798)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (20791)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (20792)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (20813)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (20801)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (20807)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (20812)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (20794)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f404,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f383,f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.54    inference(resolution,[],[f116,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(flattening,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    sP0(sK2,sK3,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    v3_tops_2(sK4,sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) & v3_tops_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f37,f36,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2) & v3_tops_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2) & v3_tops_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2) & v3_tops_2(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2) & v3_tops_2(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) & v3_tops_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ~v3_tops_2(sK4,sK2,sK3) | sP0(sK2,sK3,sK4)),
% 0.21/0.54    inference(resolution,[],[f113,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_tops_2(X0,X2,X1) | sP0(X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v3_tops_2(X0,X2,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v3_tops_2(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (((v3_tops_2(X2,X0,X1) | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | ~v3_tops_2(X2,X0,X1))) | ~sP1(X2,X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((v3_tops_2(X2,X0,X1) <=> sP0(X0,X1,X2)) | ~sP1(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    sP1(sK4,sK3,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f112,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | sP1(sK4,sK3,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f111,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f81,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.21/0.54    inference(resolution,[],[f52,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    l1_struct_0(sK3)),
% 0.21/0.54    inference(resolution,[],[f56,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    l1_pre_topc(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f48,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.54    inference(resolution,[],[f52,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    l1_struct_0(sK2)),
% 0.21/0.54    inference(resolution,[],[f56,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    l1_pre_topc(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | sP1(sK4,sK3,sK2)),
% 0.21/0.54    inference(resolution,[],[f110,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.21/0.54    inference(backward_demodulation,[],[f82,f80])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.54    inference(backward_demodulation,[],[f49,f79])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(X1) | sP1(X1,sK3,sK2)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f109,f80])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK2),u1_struct_0(sK3)) | sP1(X1,sK3,sK2)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f106,f80])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK2),u1_struct_0(sK3)) | sP1(X1,sK3,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f102,f46])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | sP1(X0,X1,sK2)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f101,f79])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | sP1(X0,X1,sK2)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f99,f79])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | sP1(X0,X1,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f65,f44])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | sP1(X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(definition_folding,[],[f22,f33,f32])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    ~v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.54    inference(backward_demodulation,[],[f288,f374])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f373,f274])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(backward_demodulation,[],[f150,f273])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f272,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    v1_relat_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f69,f85])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f271,f47])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f270,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    v2_funct_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f116,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v2_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f269,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ~v2_funct_1(k2_funct_1(sK4)) | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f268,f135])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(backward_demodulation,[],[f90,f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f132,f47])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f131,f86])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f85])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f129,f121])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ~v2_funct_1(sK4) | k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    k2_struct_0(sK3) != k2_struct_0(sK3) | ~v2_funct_1(sK4) | k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(superposition,[],[f73,f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    k2_struct_0(sK3) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.21/0.54    inference(forward_demodulation,[],[f124,f79])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.21/0.54    inference(forward_demodulation,[],[f118,f80])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.21/0.54    inference(resolution,[],[f116,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f89,f47])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f88,f86])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f70,f85])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_tops_2(X0,X1,X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ~v2_funct_1(k2_funct_1(sK4)) | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f267,f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f47])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f147,f86])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f85])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(superposition,[],[f71,f133])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    ~v2_funct_1(k2_funct_1(sK4)) | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f262,f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.21/0.54    inference(backward_demodulation,[],[f93,f133])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.21/0.54    inference(subsumption_resolution,[],[f92,f47])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f86])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f72,f85])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    ~v2_funct_1(k2_funct_1(sK4)) | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f261])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    k2_struct_0(sK2) != k2_struct_0(sK2) | ~v2_funct_1(k2_funct_1(sK4)) | k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) = k2_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(superposition,[],[f73,f258])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.54    inference(forward_demodulation,[],[f257,f133])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f256,f47])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f255,f121])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f254,f85])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f253,f86])).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f252])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    k2_struct_0(sK3) != k2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(superposition,[],[f251,f125])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f250,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~v2_struct_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f78])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_struct_0(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(superposition,[],[f237,f80])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(X1),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f236,f79])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f235,f79])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f234,f79])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f232,f79])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.54    inference(resolution,[],[f55,f77])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f142,f149])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f139,f133])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)))),
% 0.21/0.54    inference(backward_demodulation,[],[f98,f133])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))) | ~v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.54    inference(subsumption_resolution,[],[f95,f90])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))) | ~v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.21/0.54    inference(resolution,[],[f93,f70])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f372,f310])).
% 0.21/0.54  fof(f310,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f309,f135])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f308,f149])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f307,f136])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4))),
% 0.21/0.54    inference(superposition,[],[f71,f273])).
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f371,f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.21/0.54    inference(backward_demodulation,[],[f151,f273])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f149])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.21/0.54    inference(forward_demodulation,[],[f138,f133])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.54    inference(backward_demodulation,[],[f97,f133])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.54    inference(subsumption_resolution,[],[f94,f90])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.21/0.54    inference(resolution,[],[f93,f72])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f370,f47])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f369,f86])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f368,f85])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    sK4 = k2_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(k2_funct_1(k2_funct_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(k2_funct_1(sK4)),k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(k2_funct_1(sK4)))),
% 0.21/0.54    inference(resolution,[],[f367,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.54  fof(f367,plain,(
% 0.21/0.54    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_funct_1(k2_funct_1(sK4)),sK4)),
% 0.21/0.54    inference(forward_demodulation,[],[f366,f273])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK4)),
% 0.21/0.54    inference(forward_demodulation,[],[f365,f133])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f364,f47])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f363,f121])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f362,f85])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f361,f86])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f360])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    k2_struct_0(sK3) != k2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.54    inference(superposition,[],[f359,f125])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)),X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f358,f45])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)),X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f356,f78])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | r2_funct_2(k2_struct_0(sK2),k2_struct_0(sK3),k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)),X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_struct_0(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(superposition,[],[f319,f80])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | r2_funct_2(k2_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(X1),X0)),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f318,f79])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f317,f79])).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f316,f79])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f314,f79])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),X0)) )),
% 0.21/0.54    inference(resolution,[],[f53,f77])).
% 0.21/0.54  % (20816)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (20808)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.55  fof(f288,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_funct_1(k2_funct_1(sK4)),sK2,sK3)),
% 0.21/0.55    inference(backward_demodulation,[],[f259,f273])).
% 0.21/0.55  fof(f259,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f231,f258])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f208,f230])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(forward_demodulation,[],[f229,f133])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f228,f47])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f227,f121])).
% 0.21/0.55  fof(f227,plain,(
% 0.21/0.55    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f226,f85])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f225,f86])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f224])).
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    k2_struct_0(sK3) != k2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4)),
% 0.21/0.55    inference(superposition,[],[f223,f125])).
% 0.21/0.55  fof(f223,plain,(
% 0.21/0.55    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f222,f45])).
% 0.21/0.55  fof(f222,plain,(
% 0.21/0.55    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | v2_struct_0(sK3)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f220,f78])).
% 0.21/0.55  fof(f220,plain,(
% 0.21/0.55    ( ! [X1] : (k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),X1) | ~v1_funct_2(X1,k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_struct_0(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.55    inference(superposition,[],[f214,f80])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(X1),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f213,f79])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f212,f79])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f211,f79])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(X1),X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f209,f79])).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v2_funct_1(X0) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0))) )),
% 0.21/0.55    inference(resolution,[],[f54,f77])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(forward_demodulation,[],[f207,f80])).
% 0.21/0.55  fof(f207,plain,(
% 0.21/0.55    k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)),
% 0.21/0.55    inference(forward_demodulation,[],[f206,f79])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(forward_demodulation,[],[f205,f80])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) | ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(forward_demodulation,[],[f204,f79])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(forward_demodulation,[],[f203,f80])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(forward_demodulation,[],[f202,f79])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f201,f87])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f200,f47])).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f199,f121])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f198,f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    ~sP0(sK3,sK2,k2_funct_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f168,f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ~v3_tops_2(k2_funct_1(sK4),sK3,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f84,f133])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ~v3_tops_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f83,f80])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ~v3_tops_2(k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f51,f79])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    ~sP0(sK3,sK2,k2_funct_1(sK4)) | v3_tops_2(k2_funct_1(sK4),sK3,sK2)),
% 0.21/0.55    inference(resolution,[],[f167,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | v3_tops_2(X0,X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    sP1(k2_funct_1(sK4),sK2,sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f166,f135])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ~v1_funct_1(k2_funct_1(sK4)) | sP1(k2_funct_1(sK4),sK2,sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f165,f149])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    ~v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(k2_funct_1(sK4)) | sP1(k2_funct_1(sK4),sK2,sK3)),
% 0.21/0.55    inference(resolution,[],[f162,f136])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK3),k2_struct_0(sK2)) | ~v1_funct_1(X0) | sP1(X0,sK2,sK3)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f161,f79])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK3),u1_struct_0(sK2)) | sP1(X0,sK2,sK3)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f159,f79])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK3),u1_struct_0(sK2)) | sP1(X0,sK2,sK3)) )),
% 0.21/0.55    inference(resolution,[],[f104,f44])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~l1_pre_topc(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X3)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k2_struct_0(sK3),u1_struct_0(X3)) | sP1(X2,X3,sK3)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f103,f80])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | sP1(X2,X3,sK3)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f100,f80])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | sP1(X2,X3,sK3)) )),
% 0.21/0.55    inference(resolution,[],[f65,f46])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) | sP0(sK3,sK2,k2_funct_1(sK4)) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | k2_struct_0(sK3) != k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_funct_1(sK4)) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.55    inference(resolution,[],[f185,f140])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    v5_pre_topc(k2_funct_1(sK4),sK3,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f123,f133])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    v5_pre_topc(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f122,f79])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f117,f80])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)),
% 0.21/0.55    inference(resolution,[],[f116,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v5_pre_topc(k2_funct_1(X2),X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(X2)),X1,X0) | sP0(X0,X1,k2_funct_1(X2)) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(X2)) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_funct_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(resolution,[],[f64,f68])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | sP0(X0,X1,X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (20794)------------------------------
% 0.21/0.55  % (20794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20794)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (20794)Memory used [KB]: 6524
% 0.21/0.55  % (20794)Time elapsed: 0.116 s
% 0.21/0.55  % (20794)------------------------------
% 0.21/0.55  % (20794)------------------------------
% 0.21/0.55  % (20811)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (20790)Success in time 0.191 s
%------------------------------------------------------------------------------
