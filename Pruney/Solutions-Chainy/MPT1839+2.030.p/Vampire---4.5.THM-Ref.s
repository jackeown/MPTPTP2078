%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 144 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  230 ( 425 expanded)
%              Number of equality atoms :   73 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f161,f167,f169,f171,f174,f176])).

fof(f176,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f125,f32])).

fof(f32,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f125,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f174,plain,
    ( spl3_1
    | spl3_2
    | spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f172,f134,f130,f127,f123])).

fof(f127,plain,
    ( spl3_2
  <=> ! [X0] : k1_tarski(X0) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f130,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f134,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f172,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = sK0
      | k1_tarski(X0) != sK0
      | r1_tarski(sK0,sK1) ) ),
    inference(superposition,[],[f49,f101])).

fof(f101,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5))
      | k1_xboole_0 = X4
      | k1_tarski(X6) != X4
      | r1_tarski(X4,X5) ) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X4,X5)
      | k1_xboole_0 = X4
      | k1_tarski(X6) != X4
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5)) ) ),
    inference(forward_demodulation,[],[f96,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f96,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k5_xboole_0(X4,X4)
      | r1_tarski(X4,X5)
      | k1_xboole_0 = X4
      | k1_tarski(X6) != X4
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5)) ) ),
    inference(superposition,[],[f53,f84])).

fof(f84,plain,(
    ! [X4,X2,X3] :
      ( k1_setfam_1(k2_tarski(X2,X3)) = X2
      | k1_xboole_0 = X2
      | k1_tarski(X4) != X2
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3)) ) ),
    inference(superposition,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ~ v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f31,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f171,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f158,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f158,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f169,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f150,f127,f156,f152])).

fof(f152,plain,
    ( spl3_5
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f150,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_zfmisc_1(sK0)
    | ~ spl3_2 ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,
    ( ! [X0] :
        ( sK0 != X0
        | v1_xboole_0(X0)
        | ~ v1_zfmisc_1(X0) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0)
        | sK0 != X0
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f146,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(X0),X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0)
        | sK0 != X0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f128,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_tarski(sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_tarski(sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f36,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f36,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( ! [X0] : k1_tarski(X0) != sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f167,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f162,f33])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f162,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f29,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f161,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f154,f30])).

fof(f30,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f154,plain,
    ( ~ v1_zfmisc_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f141,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f136,f33])).

fof(f136,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (26316)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (26328)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (26316)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f141,f161,f167,f169,f171,f174,f176])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    $false | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f125,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f13])).
% 0.20/0.47  fof(f13,conjecture,(
% 0.20/0.47    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl3_1 | spl3_2 | spl3_3 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f172,f134,f130,f127,f123])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl3_2 <=> ! [X0] : k1_tarski(X0) != sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl3_3 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0 | k1_tarski(X0) != sK0 | r1_tarski(sK0,sK1)) )),
% 0.20/0.47    inference(superposition,[],[f49,f101])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X6,X4,X5] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5)) | k1_xboole_0 = X4 | k1_tarski(X6) != X4 | r1_tarski(X4,X5)) )),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X6,X4,X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X4,X5) | k1_xboole_0 = X4 | k1_tarski(X6) != X4 | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f96,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(resolution,[],[f69,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X0,X1)) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(superposition,[],[f52,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f40,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f46,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f43,f42])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X6,X4,X5] : (k1_xboole_0 != k5_xboole_0(X4,X4) | r1_tarski(X4,X5) | k1_xboole_0 = X4 | k1_tarski(X6) != X4 | k1_xboole_0 = k1_setfam_1(k2_tarski(X4,X5))) )),
% 0.20/0.47    inference(superposition,[],[f53,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X4,X2,X3] : (k1_setfam_1(k2_tarski(X2,X3)) = X2 | k1_xboole_0 = X2 | k1_tarski(X4) != X2 | k1_xboole_0 = k1_setfam_1(k2_tarski(X2,X3))) )),
% 0.20/0.47    inference(superposition,[],[f47,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f41,f42])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f45,f48])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.20/0.47    inference(definition_unfolding,[],[f31,f42])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~spl3_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f170])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    $false | ~spl3_6),
% 0.20/0.47    inference(resolution,[],[f158,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ~v1_xboole_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    v1_xboole_0(sK0) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl3_6 <=> v1_xboole_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ~spl3_5 | spl3_6 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f150,f127,f156,f152])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl3_5 <=> v1_zfmisc_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    v1_xboole_0(sK0) | ~v1_zfmisc_1(sK0) | ~spl3_2),
% 0.20/0.47    inference(equality_resolution,[],[f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X0] : (sK0 != X0 | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) ) | ~spl3_2),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f147])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | sK0 != X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f146,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(rectify,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | sK0 != X0) ) | ~spl3_2),
% 0.20/0.47    inference(superposition,[],[f128,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2(X0),X0)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(superposition,[],[f36,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) != sK0) ) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f127])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    $false | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f162,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.20/0.47    inference(backward_demodulation,[],[f29,f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f130])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    $false | spl3_5),
% 0.20/0.47    inference(resolution,[],[f154,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v1_zfmisc_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ~v1_zfmisc_1(sK0) | spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    $false | spl3_4),
% 0.20/0.47    inference(resolution,[],[f136,f33])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f134])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (26316)------------------------------
% 0.20/0.47  % (26316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26316)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (26316)Memory used [KB]: 6140
% 0.20/0.47  % (26316)Time elapsed: 0.026 s
% 0.20/0.47  % (26316)------------------------------
% 0.20/0.47  % (26316)------------------------------
% 0.20/0.47  % (26305)Success in time 0.109 s
%------------------------------------------------------------------------------
