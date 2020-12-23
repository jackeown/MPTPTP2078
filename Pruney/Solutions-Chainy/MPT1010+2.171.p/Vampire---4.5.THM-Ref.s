%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:15 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   51 (  98 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 421 expanded)
%              Number of equality atoms :   51 ( 115 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f118,f158])).

fof(f158,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f156,f24])).

fof(f24,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f156,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK3,sK1)
    | ~ spl6_1 ),
    inference(superposition,[],[f25,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( sK2 = k1_funct_1(sK4,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f44,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_1
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f2,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f25,f93])).

fof(f93,plain,
    ( ! [X0] : sK2 = X0
    | ~ spl6_2 ),
    inference(resolution,[],[f88,f44])).

fof(f88,plain,
    ( ! [X0] : r2_hidden(sK2,X0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

% (17067)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
        | r2_hidden(sK2,X0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f27,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k1_tarski(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_2
  <=> k1_xboole_0 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f75,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f67,f72,f69])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK2)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) ) ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f21,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK2)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f22,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK2)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
      | ~ v1_funct_2(sK4,sK1,k1_tarski(sK2))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:01:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.43/0.55  % (17054)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.43/0.55  % (17069)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.43/0.55  % (17057)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.43/0.56  % (17068)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.43/0.56  % (17059)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.43/0.56  % (17053)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.43/0.56  % (17065)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.43/0.56  % (17053)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f159,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(avatar_sat_refutation,[],[f75,f118,f158])).
% 1.43/0.56  fof(f158,plain,(
% 1.43/0.56    ~spl6_1),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f157])).
% 1.43/0.56  fof(f157,plain,(
% 1.43/0.56    $false | ~spl6_1),
% 1.43/0.56    inference(subsumption_resolution,[],[f156,f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    r2_hidden(sK3,sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,plain,(
% 1.43/0.56    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f8,f14])).
% 1.43/0.56  fof(f14,plain,(
% 1.43/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f8,plain,(
% 1.43/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.43/0.56    inference(flattening,[],[f7])).
% 1.43/0.56  fof(f7,plain,(
% 1.43/0.56    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.43/0.56    inference(ennf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.43/0.56    inference(negated_conjecture,[],[f5])).
% 1.43/0.56  fof(f5,conjecture,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.43/0.56  fof(f156,plain,(
% 1.43/0.56    ~r2_hidden(sK3,sK1) | ~spl6_1),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f151])).
% 1.43/0.56  fof(f151,plain,(
% 1.43/0.56    sK2 != sK2 | ~r2_hidden(sK3,sK1) | ~spl6_1),
% 1.43/0.56    inference(superposition,[],[f25,f147])).
% 1.43/0.56  fof(f147,plain,(
% 1.43/0.56    ( ! [X0] : (sK2 = k1_funct_1(sK4,X0) | ~r2_hidden(X0,sK1)) ) | ~spl6_1),
% 1.43/0.56    inference(resolution,[],[f44,f70])).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) | ~r2_hidden(X0,sK1)) ) | ~spl6_1),
% 1.43/0.56    inference(avatar_component_clause,[],[f69])).
% 1.43/0.56  fof(f69,plain,(
% 1.43/0.56    spl6_1 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 1.43/0.56    inference(resolution,[],[f28,f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ( ! [X0] : (sP0(X0,k1_tarski(X0))) )),
% 1.43/0.56    inference(equality_resolution,[],[f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    ( ! [X0,X1] : (sP0(X0,X1) | k1_tarski(X0) != X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f20])).
% 1.43/0.56  fof(f20,plain,(
% 1.43/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_tarski(X0) != X1))),
% 1.43/0.56    inference(nnf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,plain,(
% 1.43/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP0(X0,X1))),
% 1.43/0.56    inference(definition_folding,[],[f2,f12])).
% 1.43/0.56  fof(f12,plain,(
% 1.43/0.56    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.43/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 1.43/0.56    inference(cnf_transformation,[],[f19])).
% 1.43/0.56  fof(f19,plain,(
% 1.43/0.56    ! [X0,X1] : ((sP0(X0,X1) | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f18])).
% 1.43/0.56  fof(f18,plain,(
% 1.43/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f17,plain,(
% 1.43/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.43/0.56    inference(rectify,[],[f16])).
% 1.43/0.56  fof(f16,plain,(
% 1.43/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.43/0.56    inference(nnf_transformation,[],[f12])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    sK2 != k1_funct_1(sK4,sK3)),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f118,plain,(
% 1.43/0.56    ~spl6_2),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f94])).
% 1.43/0.56  fof(f94,plain,(
% 1.43/0.56    $false | ~spl6_2),
% 1.43/0.56    inference(subsumption_resolution,[],[f25,f93])).
% 1.43/0.56  fof(f93,plain,(
% 1.43/0.56    ( ! [X0] : (sK2 = X0) ) | ~spl6_2),
% 1.43/0.56    inference(resolution,[],[f88,f44])).
% 1.43/0.56  fof(f88,plain,(
% 1.43/0.56    ( ! [X0] : (r2_hidden(sK2,X0)) ) | ~spl6_2),
% 1.43/0.56    inference(subsumption_resolution,[],[f81,f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f1])).
% 1.43/0.56  % (17067)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.43/0.56  fof(f81,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | r2_hidden(sK2,X0)) ) | ~spl6_2),
% 1.43/0.56    inference(superposition,[],[f27,f74])).
% 1.43/0.56  fof(f74,plain,(
% 1.43/0.56    k1_xboole_0 = k1_tarski(sK2) | ~spl6_2),
% 1.43/0.56    inference(avatar_component_clause,[],[f72])).
% 1.43/0.56  fof(f72,plain,(
% 1.43/0.56    spl6_2 <=> k1_xboole_0 = k1_tarski(sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,plain,(
% 1.43/0.56    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.43/0.56    inference(ennf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 1.43/0.56  fof(f75,plain,(
% 1.43/0.56    spl6_1 | spl6_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f67,f72,f69])).
% 1.43/0.56  fof(f67,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK2) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f66,f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    v1_funct_1(sK4)),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f66,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK2) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) | ~v1_funct_1(sK4)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f64,f22])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f64,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK2) | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) | ~v1_funct_2(sK4,sK1,k1_tarski(sK2)) | ~v1_funct_1(sK4)) )),
% 1.43/0.56    inference(resolution,[],[f34,f23])).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.43/0.56    inference(flattening,[],[f10])).
% 1.43/0.56  fof(f10,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.43/0.56    inference(ennf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (17053)------------------------------
% 1.43/0.56  % (17053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (17053)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (17053)Memory used [KB]: 6140
% 1.43/0.56  % (17053)Time elapsed: 0.130 s
% 1.43/0.56  % (17053)------------------------------
% 1.43/0.56  % (17053)------------------------------
% 1.43/0.56  % (17055)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.43/0.56  % (17048)Success in time 0.195 s
%------------------------------------------------------------------------------
