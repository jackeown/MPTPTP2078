%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 118 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  196 ( 410 expanded)
%              Number of equality atoms :   42 ( 101 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f22,f26,f30,f34,f38,f43,f53,f61,f67])).

fof(f67,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f65,f47])).

fof(f47,plain,
    ( k1_tarski(sK1) != k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f29,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f44,f21])).

fof(f21,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK1,X0,X1)
        | k1_xboole_0 = X1
        | k1_tarski(sK1) = k5_partfun1(X0,X1,k3_partfun1(sK1,X0,X1)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK1,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_tarski(sK1) = k5_partfun1(X0,X1,k3_partfun1(sK1,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f29,plain,
    ( k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_4
  <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f65,plain,
    ( k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f64,f17])).

fof(f17,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( ~ v1_funct_1(sK1)
    | k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f63,f52])).

fof(f52,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_8
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f63,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | k1_tarski(sK1) = k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(sK1,k1_xboole_0,k1_xboole_0))
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ v1_funct_1(X2)
        | k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_5
  <=> ! [X1,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f61,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f48,f41,f28,f24,f20,f59])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f25,f46])).

fof(f53,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f49,f41,f28,f24,f20,f51])).

fof(f49,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f21,f46])).

fof(f43,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f39,f36,f16,f41])).

fof(f36,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK1,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_tarski(sK1) = k5_partfun1(X0,X1,k3_partfun1(sK1,X0,X1)) )
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f37,f17])).

fof(f37,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f36])).

fof(f38,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f12,f36])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f34,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_tarski(X2) = k5_partfun1(k1_xboole_0,X1,k3_partfun1(X2,k1_xboole_0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

fof(f26,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f10,f24])).

fof(f10,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f22,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f9,f20])).

fof(f9,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f18,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f8,f16])).

fof(f8,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
