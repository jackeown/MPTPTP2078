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
% DateTime   : Thu Dec  3 13:19:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 133 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  231 ( 537 expanded)
%              Number of equality atoms :   76 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f275,f276,f387,f408])).

fof(f408,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f32,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f88,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_5
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f387,plain,(
    ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f385])).

fof(f385,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_9 ),
    inference(superposition,[],[f319,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f319,plain,
    ( ! [X0] : k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_9 ),
    inference(resolution,[],[f156,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f156,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f143,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f142,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f142,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f30,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f30,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f276,plain,
    ( spl3_9
    | spl3_11 ),
    inference(avatar_split_clause,[],[f196,f133,f125])).

fof(f133,plain,
    ( spl3_11
  <=> ! [X1] :
        ( k1_tarski(X1) != sK1
        | k1_tarski(X1) = sK0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f196,plain,(
    ! [X7] :
      ( sK1 != k1_tarski(X7)
      | sK0 = k1_tarski(X7)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f56,f110])).

fof(f110,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f33,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f33,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f275,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f273,f34])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f273,plain,
    ( sK0 = sK1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( sK1 != sK1
    | sK0 = sK1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f134,f206])).

fof(f206,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f205,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f205,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f201,f92])).

fof(f92,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_6
  <=> m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f201,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f97,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f97,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_7
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f134,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != sK1
        | k1_tarski(X1) = sK0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f98,plain,
    ( ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f82,f95,f86])).

fof(f82,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f93,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f81,f90,f86])).

fof(f81,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:15:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (8170)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (8170)Refutation not found, incomplete strategy% (8170)------------------------------
% 0.22/0.48  % (8170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8176)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (8170)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (8170)Memory used [KB]: 1663
% 0.22/0.48  % (8170)Time elapsed: 0.061 s
% 0.22/0.48  % (8170)------------------------------
% 0.22/0.48  % (8170)------------------------------
% 0.22/0.50  % (8176)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f409,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f93,f98,f275,f276,f387,f408])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.50  fof(f407,plain,(
% 0.22/0.50    $false | spl3_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v1_zfmisc_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~v1_zfmisc_1(sK1) | spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl3_5 <=> v1_zfmisc_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f387,plain,(
% 0.22/0.50    ~spl3_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f386])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    $false | ~spl3_9),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f385])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | ~spl3_9),
% 0.22/0.50    inference(superposition,[],[f319,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_9),
% 0.22/0.50    inference(resolution,[],[f156,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | ~spl3_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f143,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl3_9),
% 0.22/0.50    inference(resolution,[],[f142,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.22/0.50    inference(backward_demodulation,[],[f30,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl3_9 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl3_9 | spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f196,f133,f125])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl3_11 <=> ! [X1] : (k1_tarski(X1) != sK1 | k1_tarski(X1) = sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X7] : (sK1 != k1_tarski(X7) | sK0 = k1_tarski(X7) | k1_xboole_0 = sK0) )),
% 0.22/0.50    inference(superposition,[],[f56,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f33,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) = X1 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    ~spl3_6 | ~spl3_7 | ~spl3_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f274])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    $false | (~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f273,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    sK0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    sK0 = sK1 | (~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f272])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    sK1 != sK1 | sK0 = sK1 | (~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.22/0.50    inference(superposition,[],[f134,f206])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    sK1 = k1_tarski(sK2(sK1)) | (~spl3_6 | ~spl3_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f205,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    sK1 = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | (~spl3_6 | ~spl3_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f201,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    m1_subset_1(sK2(sK1),sK1) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl3_6 <=> m1_subset_1(sK2(sK1),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    sK1 = k1_tarski(sK2(sK1)) | ~m1_subset_1(sK2(sK1),sK1) | v1_xboole_0(sK1) | ~spl3_7),
% 0.22/0.50    inference(superposition,[],[f97,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl3_7 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X1] : (k1_tarski(X1) != sK1 | k1_tarski(X1) = sK0) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~spl3_5 | spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f82,f95,f86])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f31,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(rectify,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~spl3_5 | spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f81,f90,f86])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    m1_subset_1(sK2(sK1),sK1) | ~v1_zfmisc_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f31,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (8176)------------------------------
% 0.22/0.50  % (8176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8176)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (8176)Memory used [KB]: 6268
% 0.22/0.50  % (8176)Time elapsed: 0.081 s
% 0.22/0.50  % (8176)------------------------------
% 0.22/0.50  % (8176)------------------------------
% 0.22/0.50  % (8154)Success in time 0.139 s
%------------------------------------------------------------------------------
