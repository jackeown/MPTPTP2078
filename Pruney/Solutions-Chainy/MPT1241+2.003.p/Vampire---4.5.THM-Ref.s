%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 245 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  293 (1109 expanded)
%              Number of equality atoms :   51 ( 230 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f774,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f51,f89,f102,f112,f153,f167,f204,f395,f469,f518,f717,f722,f773])).

fof(f773,plain,
    ( spl4_4
    | ~ spl4_60 ),
    inference(avatar_contradiction_clause,[],[f772])).

fof(f772,plain,
    ( $false
    | spl4_4
    | ~ spl4_60 ),
    inference(trivial_inequality_removal,[],[f771])).

fof(f771,plain,
    ( sK3 != sK3
    | spl4_4
    | ~ spl4_60 ),
    inference(superposition,[],[f49,f767])).

fof(f767,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f762,f52])).

fof(f52,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v3_pre_topc(X2,X0)
                      & k1_tops_1(X0,X2) = X2 )
                    | ( k1_tops_1(X1,X3) != X3
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( k1_tops_1(X0,X2) = X2
                       => v3_pre_topc(X2,X0) )
                      & ( v3_pre_topc(X3,X1)
                       => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f762,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl4_60 ),
    inference(backward_demodulation,[],[f109,f427])).

fof(f427,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl4_60
  <=> k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f109,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(global_subsumption,[],[f25,f104])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_4
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f722,plain,(
    spl4_96 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl4_96 ),
    inference(resolution,[],[f716,f26])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f716,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_96 ),
    inference(avatar_component_clause,[],[f715])).

fof(f715,plain,
    ( spl4_96
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f717,plain,
    ( spl4_11
    | ~ spl4_18
    | ~ spl4_96
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f711,f393,f99,f715,f146,f96])).

fof(f96,plain,
    ( spl4_11
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f146,plain,
    ( spl4_18
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f99,plain,
    ( spl4_12
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f393,plain,
    ( spl4_54
  <=> k3_subset_1(u1_struct_0(sK0),sK2) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f711,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f709])).

fof(f709,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) != k3_subset_1(u1_struct_0(sK0),sK2)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl4_54 ),
    inference(superposition,[],[f29,f394])).

fof(f394,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f393])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f518,plain,
    ( ~ spl4_59
    | spl4_60
    | ~ spl4_22
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f517,f83,f198,f426,f423])).

fof(f423,plain,
    ( spl4_59
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f198,plain,
    ( spl4_22
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f83,plain,
    ( spl4_9
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f517,plain,
    ( ~ l1_pre_topc(sK1)
    | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_9 ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X2),X3),X2)
      | ~ l1_pre_topc(X2)
      | k3_subset_1(u1_struct_0(X2),X3) = k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f469,plain,(
    spl4_59 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl4_59 ),
    inference(resolution,[],[f424,f23])).

fof(f424,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_59 ),
    inference(avatar_component_clause,[],[f423])).

fof(f395,plain,
    ( ~ spl4_18
    | spl4_54
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f391,f44,f393,f146])).

fof(f44,plain,
    ( spl4_3
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f391,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f383,f138])).

fof(f138,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f110,f45])).

fof(f45,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f110,plain,(
    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(global_subsumption,[],[f27,f105])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f383,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f162,f24])).

fof(f162,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3))))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f204,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_22 ),
    inference(resolution,[],[f199,f25])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f198])).

fof(f167,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f158,f24])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(resolution,[],[f100,f33])).

fof(f100,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f153,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl4_18 ),
    inference(resolution,[],[f147,f27])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f112,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f103,f23])).

% (10717)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% (10734)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (10735)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (10737)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (10739)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (10733)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (10722)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% (10736)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (10738)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (10731)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (10725)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (10727)Refutation not found, incomplete strategy% (10727)------------------------------
% (10727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10727)Termination reason: Refutation not found, incomplete strategy

% (10727)Memory used [KB]: 10618
% (10727)Time elapsed: 0.125 s
% (10727)------------------------------
% (10727)------------------------------
% (10728)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f103,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_10 ),
    inference(resolution,[],[f87,f33])).

fof(f87,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f102,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_1 ),
    inference(avatar_split_clause,[],[f94,f37,f99,f96])).

fof(f37,plain,
    ( spl4_1
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f94,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(global_subsumption,[],[f27,f92])).

fof(f92,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(superposition,[],[f32,f53])).

fof(f53,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f34,f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f89,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f40,f86,f83])).

fof(f40,plain,
    ( spl4_2
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    inference(global_subsumption,[],[f25,f79])).

fof(f79,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    inference(superposition,[],[f31,f52])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f19,f48,f44])).

fof(f19,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f20,f48,f37])).

fof(f20,plain,
    ( sK3 != k1_tops_1(sK1,sK3)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f21,f40,f44])).

fof(f21,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f22,f40,f37])).

fof(f22,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (10740)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.49  % (10732)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.49  % (10740)Refutation not found, incomplete strategy% (10740)------------------------------
% 0.21/0.49  % (10740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10740)Memory used [KB]: 10618
% 0.21/0.49  % (10740)Time elapsed: 0.008 s
% 0.21/0.49  % (10740)------------------------------
% 0.21/0.49  % (10740)------------------------------
% 0.21/0.50  % (10729)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (10719)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (10718)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (10721)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (10727)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (10723)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (10720)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (10724)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (10726)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (10720)Refutation not found, incomplete strategy% (10720)------------------------------
% 0.21/0.52  % (10720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10720)Memory used [KB]: 10618
% 0.21/0.52  % (10720)Time elapsed: 0.097 s
% 0.21/0.52  % (10720)------------------------------
% 0.21/0.52  % (10720)------------------------------
% 0.21/0.52  % (10729)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f774,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f42,f46,f50,f51,f89,f102,f112,f153,f167,f204,f395,f469,f518,f717,f722,f773])).
% 0.21/0.52  fof(f773,plain,(
% 0.21/0.52    spl4_4 | ~spl4_60),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f772])).
% 0.21/0.52  fof(f772,plain,(
% 0.21/0.52    $false | (spl4_4 | ~spl4_60)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f771])).
% 0.21/0.52  fof(f771,plain,(
% 0.21/0.52    sK3 != sK3 | (spl4_4 | ~spl4_60)),
% 0.21/0.52    inference(superposition,[],[f49,f767])).
% 0.21/0.52  fof(f767,plain,(
% 0.21/0.52    sK3 = k1_tops_1(sK1,sK3) | ~spl4_60),
% 0.21/0.52    inference(forward_demodulation,[],[f762,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.52    inference(resolution,[],[f34,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v3_pre_topc(X2,X0) & k1_tops_1(X0,X2) = X2) | (k1_tops_1(X1,X3) != X3 & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.52  fof(f762,plain,(
% 0.21/0.52    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) | ~spl4_60),
% 0.21/0.52    inference(backward_demodulation,[],[f109,f427])).
% 0.21/0.52  fof(f427,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~spl4_60),
% 0.21/0.52    inference(avatar_component_clause,[],[f426])).
% 0.21/0.52  fof(f426,plain,(
% 0.21/0.52    spl4_60 <=> k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 0.21/0.52    inference(global_subsumption,[],[f25,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 0.21/0.52    inference(resolution,[],[f28,f23])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    sK3 != k1_tops_1(sK1,sK3) | spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl4_4 <=> sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f722,plain,(
% 0.21/0.52    spl4_96),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f721])).
% 0.21/0.52  fof(f721,plain,(
% 0.21/0.52    $false | spl4_96),
% 0.21/0.52    inference(resolution,[],[f716,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f716,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | spl4_96),
% 0.21/0.52    inference(avatar_component_clause,[],[f715])).
% 0.21/0.52  fof(f715,plain,(
% 0.21/0.52    spl4_96 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 0.21/0.52  fof(f717,plain,(
% 0.21/0.52    spl4_11 | ~spl4_18 | ~spl4_96 | ~spl4_12 | ~spl4_54),
% 0.21/0.52    inference(avatar_split_clause,[],[f711,f393,f99,f715,f146,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_11 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl4_18 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl4_12 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    spl4_54 <=> k3_subset_1(u1_struct_0(sK0),sK2) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.52  fof(f711,plain,(
% 0.21/0.52    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~spl4_54),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f709])).
% 0.21/0.52  fof(f709,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK2) != k3_subset_1(u1_struct_0(sK0),sK2) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~spl4_54),
% 0.21/0.52    inference(superposition,[],[f29,f394])).
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK2) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl4_54),
% 0.21/0.52    inference(avatar_component_clause,[],[f393])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.52  fof(f518,plain,(
% 0.21/0.52    ~spl4_59 | spl4_60 | ~spl4_22 | ~spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f517,f83,f198,f426,f423])).
% 0.21/0.52  fof(f423,plain,(
% 0.21/0.52    spl4_59 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl4_22 <=> l1_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl4_9 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f517,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_9),
% 0.21/0.52    inference(resolution,[],[f84,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~v4_pre_topc(k3_subset_1(u1_struct_0(X2),X3),X2) | ~l1_pre_topc(X2) | k3_subset_1(u1_struct_0(X2),X3) = k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.52    inference(resolution,[],[f30,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    spl4_59),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f468])).
% 0.21/0.52  fof(f468,plain,(
% 0.21/0.52    $false | spl4_59),
% 0.21/0.52    inference(resolution,[],[f424,f23])).
% 0.21/0.52  fof(f424,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | spl4_59),
% 0.21/0.52    inference(avatar_component_clause,[],[f423])).
% 0.21/0.52  fof(f395,plain,(
% 0.21/0.52    ~spl4_18 | spl4_54 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f391,f44,f393,f146])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl4_3 <=> sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK2) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.52    inference(forward_demodulation,[],[f383,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    sK2 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) | ~spl4_3),
% 0.21/0.52    inference(forward_demodulation,[],[f110,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.52    inference(global_subsumption,[],[f27,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.52    inference(resolution,[],[f28,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f383,plain,(
% 0.21/0.52    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f162,f24])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)))) | ~l1_pre_topc(X2)) )),
% 0.21/0.52    inference(resolution,[],[f56,f33])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 0.21/0.52    inference(resolution,[],[f35,f34])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    spl4_22),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    $false | spl4_22),
% 0.21/0.52    inference(resolution,[],[f199,f25])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | spl4_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f198])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl4_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    $false | spl4_12),
% 0.21/0.52    inference(resolution,[],[f158,f24])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_12),
% 0.21/0.52    inference(resolution,[],[f100,f33])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl4_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    $false | spl4_18),
% 0.21/0.52    inference(resolution,[],[f147,f27])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | spl4_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    $false | spl4_10),
% 0.21/0.52    inference(resolution,[],[f103,f23])).
% 0.21/0.52  % (10717)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (10734)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (10735)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (10737)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % (10739)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (10733)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.53  % (10722)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (10736)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (10738)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (10731)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.54  % (10725)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.54  % (10727)Refutation not found, incomplete strategy% (10727)------------------------------
% 0.21/0.54  % (10727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10727)Memory used [KB]: 10618
% 0.21/0.54  % (10727)Time elapsed: 0.125 s
% 0.21/0.54  % (10727)------------------------------
% 0.21/0.54  % (10727)------------------------------
% 0.21/0.54  % (10728)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | spl4_10),
% 0.21/0.54    inference(resolution,[],[f87,f33])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl4_10 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ~spl4_11 | ~spl4_12 | spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f94,f37,f99,f96])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    spl4_1 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    v3_pre_topc(sK2,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.54    inference(global_subsumption,[],[f27,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    v3_pre_topc(sK2,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.21/0.54    inference(superposition,[],[f32,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.21/0.54    inference(resolution,[],[f34,f24])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl4_9 | ~spl4_10 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f81,f40,f86,f83])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    spl4_2 <=> v3_pre_topc(sK3,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ~v3_pre_topc(sK3,sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 0.21/0.54    inference(global_subsumption,[],[f25,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ~v3_pre_topc(sK3,sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 0.21/0.54    inference(superposition,[],[f31,f52])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    spl4_3 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f19,f48,f44])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    sK3 != k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f20,f48,f37])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    sK3 != k1_tops_1(sK1,sK3) | ~v3_pre_topc(sK2,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    spl4_3 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f21,f40,f44])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    v3_pre_topc(sK3,sK1) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ~spl4_1 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f40,f37])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    v3_pre_topc(sK3,sK1) | ~v3_pre_topc(sK2,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (10729)------------------------------
% 0.21/0.54  % (10729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10729)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (10729)Memory used [KB]: 11129
% 0.21/0.54  % (10729)Time elapsed: 0.095 s
% 0.21/0.54  % (10729)------------------------------
% 0.21/0.54  % (10729)------------------------------
% 0.21/0.54  % (10725)Refutation not found, incomplete strategy% (10725)------------------------------
% 0.21/0.54  % (10725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10725)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10725)Memory used [KB]: 10618
% 0.21/0.54  % (10725)Time elapsed: 0.103 s
% 0.21/0.54  % (10725)------------------------------
% 0.21/0.54  % (10725)------------------------------
% 0.21/0.54  % (10716)Success in time 0.182 s
%------------------------------------------------------------------------------
