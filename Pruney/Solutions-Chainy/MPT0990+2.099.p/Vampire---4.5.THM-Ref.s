%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:45 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 570 expanded)
%              Number of leaves         :   21 ( 119 expanded)
%              Depth                    :   28
%              Number of atoms          :  723 (4009 expanded)
%              Number of equality atoms :  207 (1315 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28887)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (28877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (28884)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f151,f198,f205,f233,f281,f514,f563])).

fof(f563,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f561,f508])).

fof(f508,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f507,f46])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f507,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f506,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f506,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f505,f196])).

fof(f196,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f505,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(superposition,[],[f249,f232])).

fof(f232,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl4_7
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f249,plain,
    ( ! [X0] :
        ( k6_partfun1(sK0) != k5_relat_1(sK2,X0)
        | k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f248,f162])).

fof(f162,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f156,f81])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f65])).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f156,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_2 ),
    inference(superposition,[],[f81,f147])).

fof(f147,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_2
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f248,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f247,f142])).

fof(f142,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f247,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f246,f43])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f245,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f245,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0)
        | k2_funct_1(sK2) = X0 )
    | ~ spl4_1 ),
    inference(superposition,[],[f73,f177])).

fof(f177,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f171,f81])).

fof(f171,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_1 ),
    inference(superposition,[],[f81,f152])).

fof(f152,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f111,f142])).

fof(f111,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f91,f110])).

fof(f110,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f108,f43])).

fof(f108,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f107,f47])).

fof(f107,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f106,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f98,f48])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(superposition,[],[f51,f41])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(resolution,[],[f47,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

% (28871)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f561,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f553,f81])).

fof(f553,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f81,f520])).

fof(f520,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f189,f516])).

fof(f516,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f132,f192])).

fof(f192,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_4
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f132,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,
    ( ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f130,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f129,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f129,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f128,f39])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[],[f50,f124])).

fof(f124,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f123,f38])).

fof(f123,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f122,f49])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f120,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f117,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f42,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

% (28889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (28868)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (28885)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f189,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_3
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f514,plain,
    ( spl4_4
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f512,f77])).

fof(f77,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f512,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f511,f289])).

fof(f289,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f220,f232])).

fof(f220,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f217,f47])).

fof(f217,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f95,f49])).

fof(f95,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(resolution,[],[f40,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_1(X4)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f511,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f510,f44])).

fof(f510,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_4 ),
    inference(subsumption_resolution,[],[f509,f40])).

fof(f509,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_4 ),
    inference(resolution,[],[f351,f39])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | k1_xboole_0 = X0 )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f350,f47])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f349,f48])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f348,f49])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f345])).

fof(f345,plain,
    ( ! [X0] :
        ( sK1 != sK1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK2) )
    | spl4_4 ),
    inference(superposition,[],[f202,f41])).

fof(f202,plain,
    ( ! [X6,X4,X7,X5] :
        ( k2_relset_1(X5,X6,X4) != X6
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(sK3,X6,X7)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3))
        | ~ v1_funct_2(X4,X5,X6)
        | k1_xboole_0 = X7
        | ~ v1_funct_1(X4) )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f200,f38])).

fof(f200,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(X4,X5,X6)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,X6,X7)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3))
        | k2_relset_1(X5,X6,X4) != X6
        | k1_xboole_0 = X7
        | ~ v1_funct_1(X4) )
    | spl4_4 ),
    inference(resolution,[],[f193,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f193,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f191])).

fof(f281,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f279,f47])).

fof(f279,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f278,f40])).

fof(f278,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f277,f38])).

fof(f277,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f276,f49])).

fof(f276,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f271,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_6
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f271,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f67,f220])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f233,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f223,f230,f226])).

fof(f223,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f221,f220])).

fof(f221,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f118,f220])).

fof(f118,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f116,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f70,f65])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f116,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f42,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f205,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f40,f203])).

fof(f203,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_5 ),
    inference(resolution,[],[f197,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f197,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f86,f195,f191,f187])).

fof(f86,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(resolution,[],[f38,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f151,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f49,f149])).

fof(f149,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_1 ),
    inference(resolution,[],[f143,f69])).

fof(f143,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f148,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f105,f145,f141])).

fof(f105,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f90,f104])).

fof(f104,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f102,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f99,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f50,f41])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f47,f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (28873)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (28888)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (28880)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (28875)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (28883)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (28862)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.58  % (28863)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.73/0.59  % (28867)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.73/0.59  % (28866)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.73/0.59  % (28861)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.73/0.60  % (28865)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.73/0.60  % (28864)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.73/0.60  % (28881)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.73/0.60  % (28879)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.73/0.60  % (28869)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.90/0.61  % (28882)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.90/0.62  % (28878)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.90/0.62  % (28888)Refutation found. Thanks to Tanya!
% 1.90/0.62  % SZS status Theorem for theBenchmark
% 1.90/0.62  % SZS output start Proof for theBenchmark
% 1.90/0.62  % (28887)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.90/0.62  % (28877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.90/0.62  % (28884)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.90/0.62  fof(f564,plain,(
% 1.90/0.62    $false),
% 1.90/0.62    inference(avatar_sat_refutation,[],[f148,f151,f198,f205,f233,f281,f514,f563])).
% 1.90/0.62  fof(f563,plain,(
% 1.90/0.62    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f562])).
% 1.90/0.62  fof(f562,plain,(
% 1.90/0.62    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 1.90/0.62    inference(subsumption_resolution,[],[f561,f508])).
% 1.90/0.62  fof(f508,plain,(
% 1.90/0.62    sK1 != k1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_7)),
% 1.90/0.62    inference(subsumption_resolution,[],[f507,f46])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    sK3 != k2_funct_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f18,plain,(
% 1.90/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f17])).
% 1.90/0.62  fof(f17,plain,(
% 1.90/0.62    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f16])).
% 1.90/0.62  fof(f16,negated_conjecture,(
% 1.90/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.90/0.62    inference(negated_conjecture,[],[f15])).
% 1.90/0.62  fof(f15,conjecture,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.90/0.62  fof(f507,plain,(
% 1.90/0.62    sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_7)),
% 1.90/0.62    inference(subsumption_resolution,[],[f506,f38])).
% 1.90/0.62  fof(f38,plain,(
% 1.90/0.62    v1_funct_1(sK3)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f506,plain,(
% 1.90/0.62    sK1 != k1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_7)),
% 1.90/0.62    inference(subsumption_resolution,[],[f505,f196])).
% 1.90/0.62  fof(f196,plain,(
% 1.90/0.62    v1_relat_1(sK3) | ~spl4_5),
% 1.90/0.62    inference(avatar_component_clause,[],[f195])).
% 1.90/0.62  fof(f195,plain,(
% 1.90/0.62    spl4_5 <=> v1_relat_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.90/0.62  fof(f505,plain,(
% 1.90/0.62    sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f504])).
% 1.90/0.62  fof(f504,plain,(
% 1.90/0.62    k6_partfun1(sK0) != k6_partfun1(sK0) | sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 1.90/0.62    inference(superposition,[],[f249,f232])).
% 1.90/0.62  fof(f232,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_7),
% 1.90/0.62    inference(avatar_component_clause,[],[f230])).
% 1.90/0.62  fof(f230,plain,(
% 1.90/0.62    spl4_7 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.90/0.62  fof(f249,plain,(
% 1.90/0.62    ( ! [X0] : (k6_partfun1(sK0) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(sK2) = X0) ) | (~spl4_1 | ~spl4_2)),
% 1.90/0.62    inference(forward_demodulation,[],[f248,f162])).
% 1.90/0.62  fof(f162,plain,(
% 1.90/0.62    sK0 = k1_relat_1(sK2) | ~spl4_2),
% 1.90/0.62    inference(forward_demodulation,[],[f156,f81])).
% 1.90/0.62  fof(f81,plain,(
% 1.90/0.62    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.90/0.62    inference(definition_unfolding,[],[f71,f65])).
% 1.90/0.62  fof(f65,plain,(
% 1.90/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f11])).
% 1.90/0.62  fof(f11,axiom,(
% 1.90/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.90/0.62  fof(f71,plain,(
% 1.90/0.62    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f1])).
% 1.90/0.62  fof(f1,axiom,(
% 1.90/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.90/0.62  fof(f156,plain,(
% 1.90/0.62    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~spl4_2),
% 1.90/0.62    inference(superposition,[],[f81,f147])).
% 1.90/0.62  fof(f147,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_2),
% 1.90/0.62    inference(avatar_component_clause,[],[f145])).
% 1.90/0.62  fof(f145,plain,(
% 1.90/0.62    spl4_2 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.90/0.62  fof(f248,plain,(
% 1.90/0.62    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | ~spl4_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f247,f142])).
% 1.90/0.62  fof(f142,plain,(
% 1.90/0.62    v1_relat_1(sK2) | ~spl4_1),
% 1.90/0.62    inference(avatar_component_clause,[],[f141])).
% 1.90/0.62  fof(f141,plain,(
% 1.90/0.62    spl4_1 <=> v1_relat_1(sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.90/0.62  fof(f247,plain,(
% 1.90/0.62    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | ~spl4_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f246,f43])).
% 1.90/0.62  fof(f43,plain,(
% 1.90/0.62    v2_funct_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f246,plain,(
% 1.90/0.62    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | ~spl4_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f245,f47])).
% 1.90/0.62  fof(f47,plain,(
% 1.90/0.62    v1_funct_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f245,plain,(
% 1.90/0.62    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,X0) | k2_funct_1(sK2) = X0) ) | ~spl4_1),
% 1.90/0.62    inference(superposition,[],[f73,f177])).
% 1.90/0.62  fof(f177,plain,(
% 1.90/0.62    sK1 = k2_relat_1(sK2) | ~spl4_1),
% 1.90/0.62    inference(forward_demodulation,[],[f171,f81])).
% 1.90/0.62  fof(f171,plain,(
% 1.90/0.62    k2_relat_1(sK2) = k1_relat_1(k6_partfun1(sK1)) | ~spl4_1),
% 1.90/0.62    inference(superposition,[],[f81,f152])).
% 1.90/0.62  fof(f152,plain,(
% 1.90/0.62    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~spl4_1),
% 1.90/0.62    inference(subsumption_resolution,[],[f111,f142])).
% 1.90/0.62  fof(f111,plain,(
% 1.90/0.62    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~v1_relat_1(sK2)),
% 1.90/0.62    inference(backward_demodulation,[],[f91,f110])).
% 1.90/0.62  fof(f110,plain,(
% 1.90/0.62    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f109,f45])).
% 1.90/0.62  fof(f45,plain,(
% 1.90/0.62    k1_xboole_0 != sK1),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f109,plain,(
% 1.90/0.62    k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f108,f43])).
% 1.90/0.62  fof(f108,plain,(
% 1.90/0.62    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f107,f47])).
% 1.90/0.62  fof(f107,plain,(
% 1.90/0.62    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f106,f49])).
% 1.90/0.62  fof(f49,plain,(
% 1.90/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f106,plain,(
% 1.90/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f98,f48])).
% 1.90/0.62  fof(f48,plain,(
% 1.90/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f98,plain,(
% 1.90/0.62    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f97])).
% 1.90/0.62  fof(f97,plain,(
% 1.90/0.62    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(superposition,[],[f51,f41])).
% 1.90/0.62  fof(f41,plain,(
% 1.90/0.62    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f51,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f20,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f19])).
% 1.90/0.62  fof(f19,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f14])).
% 1.90/0.62  fof(f14,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.90/0.62  fof(f91,plain,(
% 1.90/0.62    ~v1_relat_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))),
% 1.90/0.62    inference(subsumption_resolution,[],[f89,f43])).
% 1.90/0.62  fof(f89,plain,(
% 1.90/0.62    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))),
% 1.90/0.62    inference(resolution,[],[f47,f74])).
% 1.90/0.62  fof(f74,plain,(
% 1.90/0.62    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f54,f65])).
% 1.90/0.62  fof(f54,plain,(
% 1.90/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,plain,(
% 1.90/0.62    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(flattening,[],[f23])).
% 1.90/0.62  fof(f23,plain,(
% 1.90/0.62    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.90/0.62    inference(ennf_transformation,[],[f4])).
% 1.90/0.62  fof(f4,axiom,(
% 1.90/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.90/0.62  fof(f73,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.90/0.62    inference(definition_unfolding,[],[f52,f65])).
% 1.90/0.62  fof(f52,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.90/0.62    inference(cnf_transformation,[],[f22])).
% 1.90/0.62  fof(f22,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(flattening,[],[f21])).
% 1.90/0.62  % (28871)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.90/0.62  fof(f21,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.90/0.62    inference(ennf_transformation,[],[f5])).
% 1.90/0.62  fof(f5,axiom,(
% 1.90/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.90/0.62  fof(f561,plain,(
% 1.90/0.62    sK1 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_4)),
% 1.90/0.62    inference(forward_demodulation,[],[f553,f81])).
% 1.90/0.62  fof(f553,plain,(
% 1.90/0.62    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | (~spl4_3 | ~spl4_4)),
% 1.90/0.62    inference(superposition,[],[f81,f520])).
% 1.90/0.62  fof(f520,plain,(
% 1.90/0.62    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | (~spl4_3 | ~spl4_4)),
% 1.90/0.62    inference(forward_demodulation,[],[f189,f516])).
% 1.90/0.62  fof(f516,plain,(
% 1.90/0.62    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_4),
% 1.90/0.62    inference(subsumption_resolution,[],[f132,f192])).
% 1.90/0.62  fof(f192,plain,(
% 1.90/0.62    v2_funct_1(sK3) | ~spl4_4),
% 1.90/0.62    inference(avatar_component_clause,[],[f191])).
% 1.90/0.62  fof(f191,plain,(
% 1.90/0.62    spl4_4 <=> v2_funct_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.90/0.62  fof(f132,plain,(
% 1.90/0.62    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f131,f44])).
% 1.90/0.62  fof(f44,plain,(
% 1.90/0.62    k1_xboole_0 != sK0),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f131,plain,(
% 1.90/0.62    ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f130,f38])).
% 1.90/0.62  fof(f130,plain,(
% 1.90/0.62    ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f129,f40])).
% 1.90/0.62  fof(f40,plain,(
% 1.90/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f129,plain,(
% 1.90/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    inference(subsumption_resolution,[],[f128,f39])).
% 1.90/0.62  fof(f39,plain,(
% 1.90/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f128,plain,(
% 1.90/0.62    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f125])).
% 1.90/0.62  fof(f125,plain,(
% 1.90/0.62    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    inference(superposition,[],[f50,f124])).
% 1.90/0.62  fof(f124,plain,(
% 1.90/0.62    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    inference(subsumption_resolution,[],[f123,f38])).
% 1.90/0.62  fof(f123,plain,(
% 1.90/0.62    ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    inference(subsumption_resolution,[],[f122,f49])).
% 1.90/0.62  fof(f122,plain,(
% 1.90/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    inference(subsumption_resolution,[],[f121,f48])).
% 1.90/0.62  fof(f121,plain,(
% 1.90/0.62    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    inference(subsumption_resolution,[],[f120,f47])).
% 1.90/0.62  fof(f120,plain,(
% 1.90/0.62    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    inference(subsumption_resolution,[],[f119,f40])).
% 1.90/0.63  fof(f119,plain,(
% 1.90/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.63    inference(subsumption_resolution,[],[f117,f39])).
% 1.90/0.63  fof(f117,plain,(
% 1.90/0.63    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.63    inference(resolution,[],[f42,f64])).
% 1.90/0.63  fof(f64,plain,(
% 1.90/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.90/0.63    inference(cnf_transformation,[],[f32])).
% 1.90/0.63  % (28889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.90/0.63  % (28868)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.90/0.63  % (28885)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.90/0.63  fof(f32,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.90/0.63    inference(flattening,[],[f31])).
% 1.90/0.63  fof(f31,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.90/0.63    inference(ennf_transformation,[],[f12])).
% 1.90/0.63  fof(f12,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.90/0.63  fof(f42,plain,(
% 1.90/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.90/0.63    inference(cnf_transformation,[],[f18])).
% 1.90/0.63  fof(f50,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f20])).
% 1.90/0.63  fof(f189,plain,(
% 1.90/0.63    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~spl4_3),
% 1.90/0.63    inference(avatar_component_clause,[],[f187])).
% 1.90/0.63  fof(f187,plain,(
% 1.90/0.63    spl4_3 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))),
% 1.90/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.90/0.63  fof(f514,plain,(
% 1.90/0.63    spl4_4 | ~spl4_7),
% 1.90/0.63    inference(avatar_contradiction_clause,[],[f513])).
% 1.90/0.63  fof(f513,plain,(
% 1.90/0.63    $false | (spl4_4 | ~spl4_7)),
% 1.90/0.63    inference(subsumption_resolution,[],[f512,f77])).
% 1.90/0.63  fof(f77,plain,(
% 1.90/0.63    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.90/0.63    inference(definition_unfolding,[],[f61,f65])).
% 1.90/0.63  fof(f61,plain,(
% 1.90/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f2])).
% 1.90/0.63  fof(f2,axiom,(
% 1.90/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.90/0.63  fof(f512,plain,(
% 1.90/0.63    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_4 | ~spl4_7)),
% 1.90/0.63    inference(forward_demodulation,[],[f511,f289])).
% 1.90/0.63  fof(f289,plain,(
% 1.90/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_7),
% 1.90/0.63    inference(backward_demodulation,[],[f220,f232])).
% 1.90/0.63  fof(f220,plain,(
% 1.90/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.90/0.63    inference(subsumption_resolution,[],[f217,f47])).
% 1.90/0.63  fof(f217,plain,(
% 1.90/0.63    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.90/0.63    inference(resolution,[],[f95,f49])).
% 1.90/0.63  fof(f95,plain,(
% 1.90/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 1.90/0.63    inference(subsumption_resolution,[],[f93,f38])).
% 1.90/0.63  fof(f93,plain,(
% 1.90/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK3) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 1.90/0.63    inference(resolution,[],[f40,f68])).
% 1.90/0.63  fof(f68,plain,(
% 1.90/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_1(X4) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f36])).
% 1.90/0.63  fof(f36,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.90/0.63    inference(flattening,[],[f35])).
% 1.90/0.63  fof(f35,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.90/0.63    inference(ennf_transformation,[],[f10])).
% 1.90/0.63  fof(f10,axiom,(
% 1.90/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.90/0.63  fof(f511,plain,(
% 1.90/0.63    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_4),
% 1.90/0.63    inference(subsumption_resolution,[],[f510,f44])).
% 1.90/0.63  fof(f510,plain,(
% 1.90/0.63    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | spl4_4),
% 1.90/0.63    inference(subsumption_resolution,[],[f509,f40])).
% 1.90/0.63  fof(f509,plain,(
% 1.90/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | spl4_4),
% 1.90/0.63    inference(resolution,[],[f351,f39])).
% 1.90/0.63  fof(f351,plain,(
% 1.90/0.63    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | k1_xboole_0 = X0) ) | spl4_4),
% 1.90/0.63    inference(subsumption_resolution,[],[f350,f47])).
% 1.90/0.63  fof(f350,plain,(
% 1.90/0.63    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.90/0.63    inference(subsumption_resolution,[],[f349,f48])).
% 1.90/0.63  fof(f349,plain,(
% 1.90/0.63    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.90/0.63    inference(subsumption_resolution,[],[f348,f49])).
% 1.90/0.63  fof(f348,plain,(
% 1.90/0.63    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.90/0.63    inference(trivial_inequality_removal,[],[f345])).
% 1.90/0.63  fof(f345,plain,(
% 1.90/0.63    ( ! [X0] : (sK1 != sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = X0 | ~v1_funct_1(sK2)) ) | spl4_4),
% 1.90/0.63    inference(superposition,[],[f202,f41])).
% 1.90/0.63  fof(f202,plain,(
% 1.90/0.63    ( ! [X6,X4,X7,X5] : (k2_relset_1(X5,X6,X4) != X6 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(sK3,X6,X7) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3)) | ~v1_funct_2(X4,X5,X6) | k1_xboole_0 = X7 | ~v1_funct_1(X4)) ) | spl4_4),
% 1.90/0.63    inference(subsumption_resolution,[],[f200,f38])).
% 1.90/0.63  fof(f200,plain,(
% 1.90/0.63    ( ! [X6,X4,X7,X5] : (~v1_funct_2(X4,X5,X6) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,X6,X7) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v2_funct_1(k1_partfun1(X5,X6,X6,X7,X4,sK3)) | k2_relset_1(X5,X6,X4) != X6 | k1_xboole_0 = X7 | ~v1_funct_1(X4)) ) | spl4_4),
% 1.90/0.63    inference(resolution,[],[f193,f58])).
% 1.90/0.63  fof(f58,plain,(
% 1.90/0.63    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f26])).
% 1.90/0.63  fof(f26,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.90/0.63    inference(flattening,[],[f25])).
% 1.90/0.63  fof(f25,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.90/0.63    inference(ennf_transformation,[],[f13])).
% 1.90/0.63  fof(f13,axiom,(
% 1.90/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.90/0.63  fof(f193,plain,(
% 1.90/0.63    ~v2_funct_1(sK3) | spl4_4),
% 1.90/0.63    inference(avatar_component_clause,[],[f191])).
% 1.90/0.63  fof(f281,plain,(
% 1.90/0.63    spl4_6),
% 1.90/0.63    inference(avatar_contradiction_clause,[],[f280])).
% 1.90/0.63  fof(f280,plain,(
% 1.90/0.63    $false | spl4_6),
% 1.90/0.63    inference(subsumption_resolution,[],[f279,f47])).
% 1.90/0.63  fof(f279,plain,(
% 1.90/0.63    ~v1_funct_1(sK2) | spl4_6),
% 1.90/0.63    inference(subsumption_resolution,[],[f278,f40])).
% 1.90/0.63  fof(f278,plain,(
% 1.90/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 1.90/0.63    inference(subsumption_resolution,[],[f277,f38])).
% 1.90/0.63  fof(f277,plain,(
% 1.90/0.63    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 1.90/0.63    inference(subsumption_resolution,[],[f276,f49])).
% 1.90/0.63  fof(f276,plain,(
% 1.90/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 1.90/0.63    inference(subsumption_resolution,[],[f271,f228])).
% 1.90/0.63  fof(f228,plain,(
% 1.90/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_6),
% 1.90/0.63    inference(avatar_component_clause,[],[f226])).
% 1.90/0.63  fof(f226,plain,(
% 1.90/0.63    spl4_6 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.90/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.90/0.63  fof(f271,plain,(
% 1.90/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 1.90/0.63    inference(superposition,[],[f67,f220])).
% 1.90/0.63  fof(f67,plain,(
% 1.90/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f34])).
% 1.90/0.63  fof(f34,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.90/0.63    inference(flattening,[],[f33])).
% 1.90/0.63  fof(f33,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.90/0.63    inference(ennf_transformation,[],[f9])).
% 1.90/0.63  fof(f9,axiom,(
% 1.90/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.90/0.63  fof(f233,plain,(
% 1.90/0.63    ~spl4_6 | spl4_7),
% 1.90/0.63    inference(avatar_split_clause,[],[f223,f230,f226])).
% 1.90/0.63  fof(f223,plain,(
% 1.90/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.90/0.63    inference(forward_demodulation,[],[f221,f220])).
% 1.90/0.63  fof(f221,plain,(
% 1.90/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.90/0.63    inference(backward_demodulation,[],[f118,f220])).
% 1.90/0.63  fof(f118,plain,(
% 1.90/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.90/0.63    inference(subsumption_resolution,[],[f116,f79])).
% 1.90/0.63  fof(f79,plain,(
% 1.90/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.90/0.63    inference(definition_unfolding,[],[f70,f65])).
% 1.90/0.63  fof(f70,plain,(
% 1.90/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f8])).
% 1.90/0.63  fof(f8,axiom,(
% 1.90/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.90/0.63  fof(f116,plain,(
% 1.90/0.63    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.90/0.63    inference(resolution,[],[f42,f63])).
% 1.90/0.63  fof(f63,plain,(
% 1.90/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f30])).
% 1.90/0.63  fof(f30,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(flattening,[],[f29])).
% 1.90/0.63  fof(f29,plain,(
% 1.90/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.90/0.63    inference(ennf_transformation,[],[f7])).
% 1.90/0.63  fof(f7,axiom,(
% 1.90/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.90/0.63  fof(f205,plain,(
% 1.90/0.63    spl4_5),
% 1.90/0.63    inference(avatar_contradiction_clause,[],[f204])).
% 1.90/0.63  fof(f204,plain,(
% 1.90/0.63    $false | spl4_5),
% 1.90/0.63    inference(subsumption_resolution,[],[f40,f203])).
% 1.90/0.63  fof(f203,plain,(
% 1.90/0.63    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_5),
% 1.90/0.63    inference(resolution,[],[f197,f69])).
% 1.90/0.63  fof(f69,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f37])).
% 1.90/0.63  fof(f37,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(ennf_transformation,[],[f6])).
% 1.90/0.63  fof(f6,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.90/0.63  fof(f197,plain,(
% 1.90/0.63    ~v1_relat_1(sK3) | spl4_5),
% 1.90/0.63    inference(avatar_component_clause,[],[f195])).
% 1.90/0.63  fof(f198,plain,(
% 1.90/0.63    spl4_3 | ~spl4_4 | ~spl4_5),
% 1.90/0.63    inference(avatar_split_clause,[],[f86,f195,f191,f187])).
% 1.90/0.63  fof(f86,plain,(
% 1.90/0.63    ~v1_relat_1(sK3) | ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))),
% 1.90/0.63    inference(resolution,[],[f38,f75])).
% 1.90/0.63  fof(f75,plain,(
% 1.90/0.63    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))) )),
% 1.90/0.63    inference(definition_unfolding,[],[f53,f65])).
% 1.90/0.63  fof(f53,plain,(
% 1.90/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f24])).
% 1.90/0.63  fof(f151,plain,(
% 1.90/0.63    spl4_1),
% 1.90/0.63    inference(avatar_contradiction_clause,[],[f150])).
% 1.90/0.63  fof(f150,plain,(
% 1.90/0.63    $false | spl4_1),
% 1.90/0.63    inference(subsumption_resolution,[],[f49,f149])).
% 1.90/0.63  fof(f149,plain,(
% 1.90/0.63    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_1),
% 1.90/0.63    inference(resolution,[],[f143,f69])).
% 1.90/0.63  fof(f143,plain,(
% 1.90/0.63    ~v1_relat_1(sK2) | spl4_1),
% 1.90/0.63    inference(avatar_component_clause,[],[f141])).
% 1.90/0.63  fof(f148,plain,(
% 1.90/0.63    ~spl4_1 | spl4_2),
% 1.90/0.63    inference(avatar_split_clause,[],[f105,f145,f141])).
% 1.90/0.63  fof(f105,plain,(
% 1.90/0.63    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.90/0.63    inference(backward_demodulation,[],[f90,f104])).
% 1.90/0.63  fof(f104,plain,(
% 1.90/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(subsumption_resolution,[],[f103,f45])).
% 1.90/0.63  fof(f103,plain,(
% 1.90/0.63    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(subsumption_resolution,[],[f102,f43])).
% 1.90/0.63  fof(f102,plain,(
% 1.90/0.63    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(subsumption_resolution,[],[f101,f47])).
% 1.90/0.63  fof(f101,plain,(
% 1.90/0.63    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(subsumption_resolution,[],[f100,f49])).
% 1.90/0.63  fof(f100,plain,(
% 1.90/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(subsumption_resolution,[],[f99,f48])).
% 1.90/0.63  fof(f99,plain,(
% 1.90/0.63    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(trivial_inequality_removal,[],[f96])).
% 1.90/0.63  fof(f96,plain,(
% 1.90/0.63    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.63    inference(superposition,[],[f50,f41])).
% 1.90/0.63  fof(f90,plain,(
% 1.90/0.63    ~v1_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))),
% 1.90/0.63    inference(subsumption_resolution,[],[f88,f43])).
% 1.90/0.63  fof(f88,plain,(
% 1.90/0.63    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))),
% 1.90/0.63    inference(resolution,[],[f47,f75])).
% 1.90/0.63  % SZS output end Proof for theBenchmark
% 1.90/0.63  % (28888)------------------------------
% 1.90/0.63  % (28888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.63  % (28888)Termination reason: Refutation
% 1.90/0.63  
% 1.90/0.63  % (28888)Memory used [KB]: 6780
% 1.90/0.63  % (28888)Time elapsed: 0.202 s
% 1.90/0.63  % (28888)------------------------------
% 1.90/0.63  % (28888)------------------------------
% 1.90/0.63  % (28860)Success in time 0.269 s
%------------------------------------------------------------------------------
