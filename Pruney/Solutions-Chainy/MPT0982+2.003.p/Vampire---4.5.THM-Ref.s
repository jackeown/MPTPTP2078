%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 585 expanded)
%              Number of leaves         :   30 ( 190 expanded)
%              Depth                    :   22
%              Number of atoms          :  557 (4309 expanded)
%              Number of equality atoms :  130 (1285 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f750,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f122,f128,f143,f164,f187,f200,f215,f219,f654,f747,f749])).

fof(f749,plain,(
    ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f186,f204])).

fof(f204,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f59,f137])).

fof(f137,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK1 != k2_relset_1(sK0,sK1,sK3)
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (32206)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f44,plain,
    ( ? [X4] :
        ( sK1 != k2_relset_1(sK0,sK1,sK3)
        & k1_xboole_0 != sK2
        & v2_funct_1(X4)
        & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK3)
      & k1_xboole_0 != sK2
      & v2_funct_1(sK4)
      & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f59,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f186,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_11
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f747,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_10
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_10
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f745,f182])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK3))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_10
  <=> r1_tarski(sK1,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f745,plain,
    ( r1_tarski(sK1,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f679,f668])).

fof(f668,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f436,f199])).

fof(f199,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl5_13
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f436,plain,
    ( sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f435,f61])).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f435,plain,
    ( k2_relat_1(k6_relat_1(sK1)) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f434,f223])).

fof(f223,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f127,f205])).

fof(f205,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f157,f166])).

fof(f166,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f165,f58])).

fof(f58,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f165,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f160,f54])).

fof(f54,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f160,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f55,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f55,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f127,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_6
  <=> k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f434,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f172,f108])).

fof(f108,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f113,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_4
  <=> v1_relat_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f679,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),sK2),k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(superposition,[],[f214,f647])).

fof(f647,plain,
    ( sK2 = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f312,f554])).

fof(f554,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f539,f356])).

fof(f356,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f56,f310])).

fof(f310,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f307,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f307,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f167,f52])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f161,f53])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f55,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f56,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f539,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f361,f77])).

fof(f361,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f360,f50])).

fof(f360,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f359,f52])).

fof(f359,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f358,f53])).

fof(f358,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f357,f55])).

fof(f357,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f87,f310])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f312,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f170,f98])).

fof(f98,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f108,f63])).

fof(f214,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl5_15
  <=> ! [X0] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f654,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_12 ),
    inference(subsumption_resolution,[],[f652,f98])).

fof(f652,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_3
    | spl5_12 ),
    inference(subsumption_resolution,[],[f651,f108])).

fof(f651,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f648,f195])).

% (32211)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f195,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_12
  <=> r1_tarski(sK2,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f648,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f62,f554])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f219,plain,
    ( ~ spl5_3
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl5_3
    | spl5_14 ),
    inference(subsumption_resolution,[],[f217,f108])).

fof(f217,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f216,f53])).

fof(f216,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_14 ),
    inference(resolution,[],[f211,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f211,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl5_14
  <=> v1_funct_1(k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f215,plain,
    ( ~ spl5_14
    | spl5_15
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f207,f120,f111,f213,f209])).

fof(f120,plain,
    ( spl5_5
  <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f207,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f206,f113])).

fof(f206,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0)
        | ~ v1_funct_1(k2_funct_1(sK4))
        | ~ v1_relat_1(k2_funct_1(sK4)) )
    | ~ spl5_5 ),
    inference(superposition,[],[f70,f121])).

fof(f121,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f200,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f191,f107,f197,f193])).

fof(f191,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ spl5_3 ),
    inference(resolution,[],[f176,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f176,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f175,f108])).

fof(f175,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f159,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f159,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f55,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f187,plain,
    ( ~ spl5_10
    | spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f178,f97,f184,f180])).

fof(f178,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ r1_tarski(sK1,k2_relat_1(sK3))
    | ~ spl5_1 ),
    inference(resolution,[],[f174,f74])).

fof(f174,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f173,f98])).

fof(f173,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f138,f68])).

fof(f138,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f52,f78])).

fof(f164,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f156,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f156,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f55,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f143,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f135,f99])).

fof(f99,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f75])).

fof(f128,plain,
    ( ~ spl5_3
    | spl5_6 ),
    inference(avatar_split_clause,[],[f123,f125,f107])).

fof(f123,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f116,f53])).

fof(f116,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f57,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f122,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f118,f120,f107])).

fof(f118,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,(
    ! [X0] :
      ( k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f57,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f114,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f105,f111,f107])).

fof(f105,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (32210)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (32212)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (32205)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (32209)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (32219)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (32227)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (32215)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (32230)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (32223)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (32204)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (32228)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (32225)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (32218)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (32222)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (32226)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (32208)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.57  % (32205)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (32221)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.57  % (32207)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (32217)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.57  % (32229)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.57  % (32213)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.58  % (32220)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 1.70/0.58  fof(f750,plain,(
% 1.70/0.58    $false),
% 1.70/0.58    inference(avatar_sat_refutation,[],[f114,f122,f128,f143,f164,f187,f200,f215,f219,f654,f747,f749])).
% 1.70/0.58  fof(f749,plain,(
% 1.70/0.58    ~spl5_11),
% 1.70/0.58    inference(avatar_contradiction_clause,[],[f748])).
% 1.70/0.58  fof(f748,plain,(
% 1.70/0.58    $false | ~spl5_11),
% 1.70/0.58    inference(subsumption_resolution,[],[f186,f204])).
% 1.70/0.58  fof(f204,plain,(
% 1.70/0.58    sK1 != k2_relat_1(sK3)),
% 1.70/0.58    inference(superposition,[],[f59,f137])).
% 1.70/0.58  fof(f137,plain,(
% 1.70/0.58    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.70/0.58    inference(resolution,[],[f52,f77])).
% 1.70/0.58  fof(f77,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f35])).
% 1.70/0.58  fof(f35,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.58    inference(ennf_transformation,[],[f13])).
% 1.70/0.58  fof(f13,axiom,(
% 1.70/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.70/0.58  fof(f52,plain,(
% 1.70/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.70/0.58    inference(cnf_transformation,[],[f45])).
% 1.70/0.58  fof(f45,plain,(
% 1.70/0.58    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f44,f43])).
% 1.70/0.58  fof(f43,plain,(
% 1.70/0.58    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.59  % (32206)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.70/0.59  fof(f44,plain,(
% 1.70/0.59    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f21,plain,(
% 1.70/0.59    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.70/0.59    inference(flattening,[],[f20])).
% 1.70/0.59  fof(f20,plain,(
% 1.70/0.59    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.70/0.59    inference(ennf_transformation,[],[f18])).
% 1.70/0.59  fof(f18,negated_conjecture,(
% 1.70/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.70/0.59    inference(negated_conjecture,[],[f17])).
% 1.70/0.59  fof(f17,conjecture,(
% 1.70/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.70/0.59  fof(f59,plain,(
% 1.70/0.59    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f186,plain,(
% 1.70/0.59    sK1 = k2_relat_1(sK3) | ~spl5_11),
% 1.70/0.59    inference(avatar_component_clause,[],[f184])).
% 1.70/0.59  fof(f184,plain,(
% 1.70/0.59    spl5_11 <=> sK1 = k2_relat_1(sK3)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.70/0.59  fof(f747,plain,(
% 1.70/0.59    ~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_10 | ~spl5_13 | ~spl5_15),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f746])).
% 1.70/0.59  fof(f746,plain,(
% 1.70/0.59    $false | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_10 | ~spl5_13 | ~spl5_15)),
% 1.70/0.59    inference(subsumption_resolution,[],[f745,f182])).
% 1.70/0.59  fof(f182,plain,(
% 1.70/0.59    ~r1_tarski(sK1,k2_relat_1(sK3)) | spl5_10),
% 1.70/0.59    inference(avatar_component_clause,[],[f180])).
% 1.70/0.59  fof(f180,plain,(
% 1.70/0.59    spl5_10 <=> r1_tarski(sK1,k2_relat_1(sK3))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.70/0.59  fof(f745,plain,(
% 1.70/0.59    r1_tarski(sK1,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_13 | ~spl5_15)),
% 1.70/0.59    inference(forward_demodulation,[],[f679,f668])).
% 1.70/0.59  fof(f668,plain,(
% 1.70/0.59    sK1 = k9_relat_1(k2_funct_1(sK4),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_13)),
% 1.70/0.59    inference(backward_demodulation,[],[f436,f199])).
% 1.70/0.59  fof(f199,plain,(
% 1.70/0.59    sK2 = k2_relat_1(sK4) | ~spl5_13),
% 1.70/0.59    inference(avatar_component_clause,[],[f197])).
% 1.70/0.59  fof(f197,plain,(
% 1.70/0.59    spl5_13 <=> sK2 = k2_relat_1(sK4)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.70/0.59  fof(f436,plain,(
% 1.70/0.59    sK1 = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_3 | ~spl5_4 | ~spl5_6)),
% 1.70/0.59    inference(forward_demodulation,[],[f435,f61])).
% 1.70/0.59  fof(f61,plain,(
% 1.70/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.70/0.59  fof(f435,plain,(
% 1.70/0.59    k2_relat_1(k6_relat_1(sK1)) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_3 | ~spl5_4 | ~spl5_6)),
% 1.70/0.59    inference(forward_demodulation,[],[f434,f223])).
% 1.70/0.59  fof(f223,plain,(
% 1.70/0.59    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1) | ~spl5_6),
% 1.70/0.59    inference(forward_demodulation,[],[f127,f205])).
% 1.70/0.59  fof(f205,plain,(
% 1.70/0.59    sK1 = k1_relat_1(sK4)),
% 1.70/0.59    inference(forward_demodulation,[],[f157,f166])).
% 1.70/0.59  fof(f166,plain,(
% 1.70/0.59    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f165,f58])).
% 1.70/0.59  fof(f58,plain,(
% 1.70/0.59    k1_xboole_0 != sK2),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f165,plain,(
% 1.70/0.59    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f160,f54])).
% 1.70/0.59  fof(f54,plain,(
% 1.70/0.59    v1_funct_2(sK4,sK1,sK2)),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f160,plain,(
% 1.70/0.59    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.70/0.59    inference(resolution,[],[f55,f79])).
% 1.70/0.59  fof(f79,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f49])).
% 1.70/0.59  fof(f49,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.59    inference(nnf_transformation,[],[f38])).
% 1.70/0.59  fof(f38,plain,(
% 1.70/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.59    inference(flattening,[],[f37])).
% 1.70/0.59  fof(f37,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.59    inference(ennf_transformation,[],[f14])).
% 1.70/0.59  fof(f14,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f157,plain,(
% 1.70/0.59    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.70/0.59    inference(resolution,[],[f55,f76])).
% 1.70/0.59  fof(f76,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f34])).
% 1.70/0.59  fof(f34,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.59    inference(ennf_transformation,[],[f12])).
% 1.70/0.59  fof(f12,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.70/0.59  fof(f127,plain,(
% 1.70/0.59    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) | ~spl5_6),
% 1.70/0.59    inference(avatar_component_clause,[],[f125])).
% 1.70/0.59  fof(f125,plain,(
% 1.70/0.59    spl5_6 <=> k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.70/0.59  fof(f434,plain,(
% 1.70/0.59    k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) | (~spl5_3 | ~spl5_4)),
% 1.70/0.59    inference(resolution,[],[f172,f108])).
% 1.70/0.59  fof(f108,plain,(
% 1.70/0.59    v1_relat_1(sK4) | ~spl5_3),
% 1.70/0.59    inference(avatar_component_clause,[],[f107])).
% 1.70/0.59  fof(f107,plain,(
% 1.70/0.59    spl5_3 <=> v1_relat_1(sK4)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.70/0.59  fof(f172,plain,(
% 1.70/0.59    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) = k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0))) ) | ~spl5_4),
% 1.70/0.59    inference(resolution,[],[f113,f63])).
% 1.70/0.59  fof(f63,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f23])).
% 1.70/0.59  fof(f23,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.70/0.59  fof(f113,plain,(
% 1.70/0.59    v1_relat_1(k2_funct_1(sK4)) | ~spl5_4),
% 1.70/0.59    inference(avatar_component_clause,[],[f111])).
% 1.70/0.59  fof(f111,plain,(
% 1.70/0.59    spl5_4 <=> v1_relat_1(k2_funct_1(sK4))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.70/0.59  fof(f679,plain,(
% 1.70/0.59    r1_tarski(k9_relat_1(k2_funct_1(sK4),sK2),k2_relat_1(sK3)) | (~spl5_1 | ~spl5_3 | ~spl5_15)),
% 1.70/0.59    inference(superposition,[],[f214,f647])).
% 1.70/0.59  fof(f647,plain,(
% 1.70/0.59    sK2 = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_3)),
% 1.70/0.59    inference(backward_demodulation,[],[f312,f554])).
% 1.70/0.59  fof(f554,plain,(
% 1.70/0.59    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 1.70/0.59    inference(forward_demodulation,[],[f539,f356])).
% 1.70/0.59  fof(f356,plain,(
% 1.70/0.59    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.70/0.59    inference(backward_demodulation,[],[f56,f310])).
% 1.70/0.59  fof(f310,plain,(
% 1.70/0.59    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f307,f50])).
% 1.70/0.59  fof(f50,plain,(
% 1.70/0.59    v1_funct_1(sK3)),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f307,plain,(
% 1.70/0.59    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.70/0.59    inference(resolution,[],[f167,f52])).
% 1.70/0.59  fof(f167,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f161,f53])).
% 1.70/0.59  fof(f53,plain,(
% 1.70/0.59    v1_funct_1(sK4)),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f161,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.70/0.59    inference(resolution,[],[f55,f85])).
% 1.70/0.59  fof(f85,plain,(
% 1.70/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f40])).
% 1.70/0.59  fof(f40,plain,(
% 1.70/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.70/0.59    inference(flattening,[],[f39])).
% 1.70/0.59  fof(f39,plain,(
% 1.70/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.70/0.59    inference(ennf_transformation,[],[f16])).
% 1.70/0.59  fof(f16,axiom,(
% 1.70/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.70/0.59  fof(f56,plain,(
% 1.70/0.59    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f539,plain,(
% 1.70/0.59    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.70/0.59    inference(resolution,[],[f361,f77])).
% 1.70/0.59  fof(f361,plain,(
% 1.70/0.59    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.70/0.59    inference(subsumption_resolution,[],[f360,f50])).
% 1.70/0.59  fof(f360,plain,(
% 1.70/0.59    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 1.70/0.59    inference(subsumption_resolution,[],[f359,f52])).
% 1.70/0.59  fof(f359,plain,(
% 1.70/0.59    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.70/0.59    inference(subsumption_resolution,[],[f358,f53])).
% 1.70/0.59  fof(f358,plain,(
% 1.70/0.59    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.70/0.59    inference(subsumption_resolution,[],[f357,f55])).
% 1.70/0.59  fof(f357,plain,(
% 1.70/0.59    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.70/0.59    inference(superposition,[],[f87,f310])).
% 1.70/0.59  fof(f87,plain,(
% 1.70/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f42])).
% 1.70/0.59  fof(f42,plain,(
% 1.70/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.70/0.59    inference(flattening,[],[f41])).
% 1.70/0.59  fof(f41,plain,(
% 1.70/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.70/0.59    inference(ennf_transformation,[],[f15])).
% 1.70/0.59  fof(f15,axiom,(
% 1.70/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.70/0.59  fof(f312,plain,(
% 1.70/0.59    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_3)),
% 1.70/0.59    inference(resolution,[],[f170,f98])).
% 1.70/0.59  fof(f98,plain,(
% 1.70/0.59    v1_relat_1(sK3) | ~spl5_1),
% 1.70/0.59    inference(avatar_component_clause,[],[f97])).
% 1.70/0.59  fof(f97,plain,(
% 1.70/0.59    spl5_1 <=> v1_relat_1(sK3)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.70/0.59  fof(f170,plain,(
% 1.70/0.59    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) ) | ~spl5_3),
% 1.70/0.59    inference(resolution,[],[f108,f63])).
% 1.70/0.59  fof(f214,plain,(
% 1.70/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0)) ) | ~spl5_15),
% 1.70/0.59    inference(avatar_component_clause,[],[f213])).
% 1.70/0.59  fof(f213,plain,(
% 1.70/0.59    spl5_15 <=> ! [X0] : r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.70/0.59  fof(f654,plain,(
% 1.70/0.59    ~spl5_1 | ~spl5_3 | spl5_12),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f653])).
% 1.70/0.59  fof(f653,plain,(
% 1.70/0.59    $false | (~spl5_1 | ~spl5_3 | spl5_12)),
% 1.70/0.59    inference(subsumption_resolution,[],[f652,f98])).
% 1.70/0.59  fof(f652,plain,(
% 1.70/0.59    ~v1_relat_1(sK3) | (~spl5_3 | spl5_12)),
% 1.70/0.59    inference(subsumption_resolution,[],[f651,f108])).
% 1.70/0.59  fof(f651,plain,(
% 1.70/0.59    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl5_12),
% 1.70/0.59    inference(subsumption_resolution,[],[f648,f195])).
% 1.70/0.59  % (32211)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.70/0.59  fof(f195,plain,(
% 1.70/0.59    ~r1_tarski(sK2,k2_relat_1(sK4)) | spl5_12),
% 1.70/0.59    inference(avatar_component_clause,[],[f193])).
% 1.70/0.59  fof(f193,plain,(
% 1.70/0.59    spl5_12 <=> r1_tarski(sK2,k2_relat_1(sK4))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.70/0.59  fof(f648,plain,(
% 1.70/0.59    r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 1.70/0.59    inference(superposition,[],[f62,f554])).
% 1.70/0.59  fof(f62,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f22])).
% 1.70/0.59  fof(f22,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f4])).
% 1.70/0.59  fof(f4,axiom,(
% 1.70/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.70/0.59  fof(f219,plain,(
% 1.70/0.59    ~spl5_3 | spl5_14),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f218])).
% 1.70/0.59  fof(f218,plain,(
% 1.70/0.59    $false | (~spl5_3 | spl5_14)),
% 1.70/0.59    inference(subsumption_resolution,[],[f217,f108])).
% 1.70/0.59  fof(f217,plain,(
% 1.70/0.59    ~v1_relat_1(sK4) | spl5_14),
% 1.70/0.59    inference(subsumption_resolution,[],[f216,f53])).
% 1.70/0.59  fof(f216,plain,(
% 1.70/0.59    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_14),
% 1.70/0.59    inference(resolution,[],[f211,f65])).
% 1.70/0.59  fof(f65,plain,(
% 1.70/0.59    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f25])).
% 1.70/0.59  fof(f25,plain,(
% 1.70/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.59    inference(flattening,[],[f24])).
% 1.70/0.59  fof(f24,plain,(
% 1.70/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f6])).
% 1.70/0.59  fof(f6,axiom,(
% 1.70/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.70/0.59  fof(f211,plain,(
% 1.70/0.59    ~v1_funct_1(k2_funct_1(sK4)) | spl5_14),
% 1.70/0.59    inference(avatar_component_clause,[],[f209])).
% 1.70/0.59  fof(f209,plain,(
% 1.70/0.59    spl5_14 <=> v1_funct_1(k2_funct_1(sK4))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.70/0.59  fof(f215,plain,(
% 1.70/0.59    ~spl5_14 | spl5_15 | ~spl5_4 | ~spl5_5),
% 1.70/0.59    inference(avatar_split_clause,[],[f207,f120,f111,f213,f209])).
% 1.70/0.59  fof(f120,plain,(
% 1.70/0.59    spl5_5 <=> ! [X0] : k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.70/0.59  fof(f207,plain,(
% 1.70/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) | ~v1_funct_1(k2_funct_1(sK4))) ) | (~spl5_4 | ~spl5_5)),
% 1.70/0.59    inference(subsumption_resolution,[],[f206,f113])).
% 1.70/0.59  fof(f206,plain,(
% 1.70/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) | ~v1_funct_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))) ) | ~spl5_5),
% 1.70/0.59    inference(superposition,[],[f70,f121])).
% 1.70/0.59  fof(f121,plain,(
% 1.70/0.59    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0)) ) | ~spl5_5),
% 1.70/0.59    inference(avatar_component_clause,[],[f120])).
% 1.70/0.59  fof(f70,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(flattening,[],[f29])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.70/0.59    inference(ennf_transformation,[],[f7])).
% 1.70/0.59  fof(f7,axiom,(
% 1.70/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.70/0.59  fof(f200,plain,(
% 1.70/0.59    ~spl5_12 | spl5_13 | ~spl5_3),
% 1.70/0.59    inference(avatar_split_clause,[],[f191,f107,f197,f193])).
% 1.70/0.59  fof(f191,plain,(
% 1.70/0.59    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~spl5_3),
% 1.70/0.59    inference(resolution,[],[f176,f74])).
% 1.70/0.59  fof(f74,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f48])).
% 1.70/0.59  fof(f48,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(flattening,[],[f47])).
% 1.70/0.59  fof(f47,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(nnf_transformation,[],[f1])).
% 1.70/0.59  fof(f1,axiom,(
% 1.70/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.59  fof(f176,plain,(
% 1.70/0.59    r1_tarski(k2_relat_1(sK4),sK2) | ~spl5_3),
% 1.70/0.59    inference(subsumption_resolution,[],[f175,f108])).
% 1.70/0.59  fof(f175,plain,(
% 1.70/0.59    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 1.70/0.59    inference(resolution,[],[f159,f68])).
% 1.70/0.59  fof(f68,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f46])).
% 1.70/0.59  fof(f46,plain,(
% 1.70/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(nnf_transformation,[],[f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f2])).
% 1.70/0.59  fof(f2,axiom,(
% 1.70/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.70/0.59  fof(f159,plain,(
% 1.70/0.59    v5_relat_1(sK4,sK2)),
% 1.70/0.59    inference(resolution,[],[f55,f78])).
% 1.70/0.59  fof(f78,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f36])).
% 1.70/0.59  fof(f36,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.59    inference(ennf_transformation,[],[f19])).
% 1.70/0.59  fof(f19,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.70/0.59    inference(pure_predicate_removal,[],[f11])).
% 1.70/0.59  fof(f11,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.70/0.59  fof(f187,plain,(
% 1.70/0.59    ~spl5_10 | spl5_11 | ~spl5_1),
% 1.70/0.59    inference(avatar_split_clause,[],[f178,f97,f184,f180])).
% 1.70/0.59  fof(f178,plain,(
% 1.70/0.59    sK1 = k2_relat_1(sK3) | ~r1_tarski(sK1,k2_relat_1(sK3)) | ~spl5_1),
% 1.70/0.59    inference(resolution,[],[f174,f74])).
% 1.70/0.59  fof(f174,plain,(
% 1.70/0.59    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_1),
% 1.70/0.59    inference(subsumption_resolution,[],[f173,f98])).
% 1.70/0.59  fof(f173,plain,(
% 1.70/0.59    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.70/0.59    inference(resolution,[],[f138,f68])).
% 1.70/0.59  fof(f138,plain,(
% 1.70/0.59    v5_relat_1(sK3,sK1)),
% 1.70/0.59    inference(resolution,[],[f52,f78])).
% 1.70/0.59  fof(f164,plain,(
% 1.70/0.59    spl5_3),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f163])).
% 1.70/0.59  fof(f163,plain,(
% 1.70/0.59    $false | spl5_3),
% 1.70/0.59    inference(subsumption_resolution,[],[f156,f109])).
% 1.70/0.59  fof(f109,plain,(
% 1.70/0.59    ~v1_relat_1(sK4) | spl5_3),
% 1.70/0.59    inference(avatar_component_clause,[],[f107])).
% 1.70/0.59  fof(f156,plain,(
% 1.70/0.59    v1_relat_1(sK4)),
% 1.70/0.59    inference(resolution,[],[f55,f75])).
% 1.70/0.59  fof(f75,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f33])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.70/0.59    inference(ennf_transformation,[],[f10])).
% 1.70/0.59  fof(f10,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.70/0.59  fof(f143,plain,(
% 1.70/0.59    spl5_1),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f142])).
% 1.70/0.59  fof(f142,plain,(
% 1.70/0.59    $false | spl5_1),
% 1.70/0.59    inference(subsumption_resolution,[],[f135,f99])).
% 1.70/0.59  fof(f99,plain,(
% 1.70/0.59    ~v1_relat_1(sK3) | spl5_1),
% 1.70/0.59    inference(avatar_component_clause,[],[f97])).
% 1.70/0.59  fof(f135,plain,(
% 1.70/0.59    v1_relat_1(sK3)),
% 1.70/0.59    inference(resolution,[],[f52,f75])).
% 1.70/0.59  fof(f128,plain,(
% 1.70/0.59    ~spl5_3 | spl5_6),
% 1.70/0.59    inference(avatar_split_clause,[],[f123,f125,f107])).
% 1.70/0.59  fof(f123,plain,(
% 1.70/0.59    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.70/0.59    inference(subsumption_resolution,[],[f116,f53])).
% 1.70/0.59  fof(f116,plain,(
% 1.70/0.59    k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.70/0.59    inference(resolution,[],[f57,f66])).
% 1.70/0.59  fof(f66,plain,(
% 1.70/0.59    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.70/0.59    inference(flattening,[],[f26])).
% 1.70/0.59  fof(f26,plain,(
% 1.70/0.59    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f9])).
% 1.70/0.59  fof(f9,axiom,(
% 1.70/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.70/0.59  fof(f57,plain,(
% 1.70/0.59    v2_funct_1(sK4)),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f122,plain,(
% 1.70/0.59    ~spl5_3 | spl5_5),
% 1.70/0.59    inference(avatar_split_clause,[],[f118,f120,f107])).
% 1.70/0.59  fof(f118,plain,(
% 1.70/0.59    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_relat_1(sK4)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f115,f53])).
% 1.70/0.59  fof(f115,plain,(
% 1.70/0.59    ( ! [X0] : (k9_relat_1(sK4,X0) = k10_relat_1(k2_funct_1(sK4),X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.70/0.59    inference(resolution,[],[f57,f71])).
% 1.70/0.59  fof(f71,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.70/0.59    inference(flattening,[],[f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.70/0.59    inference(ennf_transformation,[],[f8])).
% 1.70/0.59  fof(f8,axiom,(
% 1.70/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.70/0.59  fof(f114,plain,(
% 1.70/0.59    ~spl5_3 | spl5_4),
% 1.70/0.59    inference(avatar_split_clause,[],[f105,f111,f107])).
% 1.70/0.59  fof(f105,plain,(
% 1.70/0.59    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(sK4)),
% 1.70/0.59    inference(resolution,[],[f53,f64])).
% 1.70/0.59  fof(f64,plain,(
% 1.70/0.59    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f25])).
% 1.70/0.59  % SZS output end Proof for theBenchmark
% 1.70/0.59  % (32205)------------------------------
% 1.70/0.59  % (32205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (32205)Termination reason: Refutation
% 1.70/0.59  
% 1.70/0.59  % (32205)Memory used [KB]: 11129
% 1.70/0.59  % (32205)Time elapsed: 0.130 s
% 1.70/0.59  % (32205)------------------------------
% 1.70/0.59  % (32205)------------------------------
% 1.70/0.60  % (32203)Success in time 0.233 s
%------------------------------------------------------------------------------
