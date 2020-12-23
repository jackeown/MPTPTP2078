%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:14 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 130 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 386 expanded)
%              Number of equality atoms :   62 ( 117 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f108,f128,f134,f143])).

fof(f143,plain,
    ( ~ spl5_2
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f58,f63,f136])).

fof(f136,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f103,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f103,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_7
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f63,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_3
  <=> sK1 = k1_funct_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f58,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f134,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f34,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_10
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f128,plain,
    ( ~ spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f114,f105,f125])).

fof(f105,plain,
    ( spl5_8
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f114,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(superposition,[],[f77,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f77,plain,(
    ! [X0] : ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(superposition,[],[f46,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f108,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_7
    | spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f86,f71,f105,f102,f66,f51])).

fof(f51,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f71,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ v1_funct_1(sK3) )
    | ~ spl5_5 ),
    inference(resolution,[],[f31,f73])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f74,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f69,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12855)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (12847)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (12839)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (12837)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.52  % (12855)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % (12844)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f144,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f108,f128,f134,f143])).
% 1.22/0.52  fof(f143,plain,(
% 1.22/0.52    ~spl5_2 | spl5_3 | ~spl5_7),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f138])).
% 1.22/0.52  fof(f138,plain,(
% 1.22/0.52    $false | (~spl5_2 | spl5_3 | ~spl5_7)),
% 1.22/0.52    inference(unit_resulting_resolution,[],[f58,f63,f136])).
% 1.22/0.52  fof(f136,plain,(
% 1.22/0.52    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK0)) ) | ~spl5_7),
% 1.22/0.52    inference(resolution,[],[f103,f49])).
% 1.22/0.52  fof(f49,plain,(
% 1.22/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.22/0.52    inference(equality_resolution,[],[f45])).
% 1.22/0.52  fof(f45,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.22/0.52    inference(definition_unfolding,[],[f27,f39])).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f33,f38])).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f36,f37])).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.22/0.52    inference(rectify,[],[f18])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.22/0.52    inference(nnf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.22/0.52  fof(f103,plain,(
% 1.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_7),
% 1.22/0.52    inference(avatar_component_clause,[],[f102])).
% 1.22/0.52  fof(f102,plain,(
% 1.22/0.52    spl5_7 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.22/0.52  fof(f63,plain,(
% 1.22/0.52    sK1 != k1_funct_1(sK3,sK2) | spl5_3),
% 1.22/0.52    inference(avatar_component_clause,[],[f61])).
% 1.22/0.52  fof(f61,plain,(
% 1.22/0.52    spl5_3 <=> sK1 = k1_funct_1(sK3,sK2)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.22/0.52  fof(f58,plain,(
% 1.22/0.52    r2_hidden(sK2,sK0) | ~spl5_2),
% 1.22/0.52    inference(avatar_component_clause,[],[f56])).
% 1.22/0.52  fof(f56,plain,(
% 1.22/0.52    spl5_2 <=> r2_hidden(sK2,sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.22/0.52  fof(f134,plain,(
% 1.22/0.52    spl5_10),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f131])).
% 1.22/0.52  fof(f131,plain,(
% 1.22/0.52    $false | spl5_10),
% 1.22/0.52    inference(unit_resulting_resolution,[],[f34,f127])).
% 1.22/0.52  fof(f127,plain,(
% 1.22/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl5_10),
% 1.22/0.52    inference(avatar_component_clause,[],[f125])).
% 1.22/0.52  fof(f125,plain,(
% 1.22/0.52    spl5_10 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.22/0.52  fof(f128,plain,(
% 1.22/0.52    ~spl5_10 | ~spl5_8),
% 1.22/0.52    inference(avatar_split_clause,[],[f114,f105,f125])).
% 1.22/0.52  fof(f105,plain,(
% 1.22/0.52    spl5_8 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.22/0.52  fof(f114,plain,(
% 1.22/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_8),
% 1.22/0.52    inference(superposition,[],[f77,f107])).
% 1.22/0.52  fof(f107,plain,(
% 1.22/0.52    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl5_8),
% 1.22/0.52    inference(avatar_component_clause,[],[f105])).
% 1.22/0.52  fof(f77,plain,(
% 1.22/0.52    ( ! [X0] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0)) )),
% 1.22/0.52    inference(equality_resolution,[],[f75])).
% 1.22/0.52  fof(f75,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.22/0.52    inference(superposition,[],[f46,f35])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f32,f39])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.22/0.52  fof(f108,plain,(
% 1.22/0.52    ~spl5_1 | ~spl5_4 | spl5_7 | spl5_8 | ~spl5_5),
% 1.22/0.52    inference(avatar_split_clause,[],[f86,f71,f105,f102,f66,f51])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    spl5_1 <=> v1_funct_1(sK3)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.22/0.52  fof(f66,plain,(
% 1.22/0.52    spl5_4 <=> v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.22/0.52  fof(f71,plain,(
% 1.22/0.52    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.22/0.52  fof(f86,plain,(
% 1.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3)) ) | ~spl5_5),
% 1.22/0.52    inference(resolution,[],[f31,f73])).
% 1.22/0.52  fof(f73,plain,(
% 1.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) | ~spl5_5),
% 1.22/0.52    inference(avatar_component_clause,[],[f71])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.22/0.52    inference(flattening,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.22/0.52    inference(ennf_transformation,[],[f8])).
% 1.22/0.52  fof(f8,axiom,(
% 1.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.22/0.52  fof(f74,plain,(
% 1.22/0.52    spl5_5),
% 1.22/0.52    inference(avatar_split_clause,[],[f40,f71])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.22/0.52    inference(definition_unfolding,[],[f24,f39])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.22/0.52    inference(flattening,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.22/0.52    inference(ennf_transformation,[],[f10])).
% 1.22/0.52  fof(f10,negated_conjecture,(
% 1.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.22/0.52    inference(negated_conjecture,[],[f9])).
% 1.22/0.52  fof(f9,conjecture,(
% 1.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.22/0.52  fof(f69,plain,(
% 1.22/0.52    spl5_4),
% 1.22/0.52    inference(avatar_split_clause,[],[f41,f66])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.22/0.52    inference(definition_unfolding,[],[f23,f39])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f64,plain,(
% 1.22/0.52    ~spl5_3),
% 1.22/0.52    inference(avatar_split_clause,[],[f26,f61])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    sK1 != k1_funct_1(sK3,sK2)),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f59,plain,(
% 1.22/0.52    spl5_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f25,f56])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    r2_hidden(sK2,sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f54,plain,(
% 1.22/0.52    spl5_1),
% 1.22/0.52    inference(avatar_split_clause,[],[f22,f51])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    v1_funct_1(sK3)),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (12855)------------------------------
% 1.22/0.52  % (12855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (12855)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (12855)Memory used [KB]: 10746
% 1.22/0.52  % (12855)Time elapsed: 0.059 s
% 1.22/0.52  % (12855)------------------------------
% 1.22/0.52  % (12855)------------------------------
% 1.22/0.52  % (12831)Success in time 0.162 s
%------------------------------------------------------------------------------
