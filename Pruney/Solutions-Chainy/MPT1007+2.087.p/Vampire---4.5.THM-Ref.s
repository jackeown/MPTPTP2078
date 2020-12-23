%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:04 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   51 (  87 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 303 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f77])).

fof(f77,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f43,f48,f53,f67,f58,f63,f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

% (11851)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f37,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f53,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

% (11845)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f56])).

fof(f34,plain,(
    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f19,f32])).

fof(f19,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.58/0.58  % (11867)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.58/0.58  % (11859)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.58/0.59  % (11867)Refutation found. Thanks to Tanya!
% 1.58/0.59  % SZS status Theorem for theBenchmark
% 1.58/0.59  % SZS output start Proof for theBenchmark
% 1.58/0.59  fof(f78,plain,(
% 1.58/0.59    $false),
% 1.58/0.59    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f77])).
% 1.58/0.59  fof(f77,plain,(
% 1.58/0.59    ~spl3_1 | spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f74])).
% 1.58/0.59  fof(f74,plain,(
% 1.58/0.59    $false | (~spl3_1 | spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5)),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f43,f48,f53,f67,f58,f63,f23])).
% 1.58/0.59  fof(f23,plain,(
% 1.58/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f11])).
% 1.58/0.59  fof(f11,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.58/0.59    inference(flattening,[],[f10])).
% 1.58/0.59  fof(f10,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.58/0.59    inference(ennf_transformation,[],[f5])).
% 1.58/0.59  % (11851)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.58/0.59  fof(f5,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.58/0.59  fof(f63,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl3_5),
% 1.58/0.59    inference(avatar_component_clause,[],[f61])).
% 1.58/0.59  fof(f61,plain,(
% 1.58/0.59    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.58/0.59  fof(f58,plain,(
% 1.58/0.59    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) | ~spl3_4),
% 1.58/0.59    inference(avatar_component_clause,[],[f56])).
% 1.58/0.59  fof(f56,plain,(
% 1.58/0.59    spl3_4 <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.58/0.59  fof(f67,plain,(
% 1.58/0.59    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 1.58/0.59    inference(resolution,[],[f37,f38])).
% 1.58/0.59  fof(f38,plain,(
% 1.58/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.59    inference(equality_resolution,[],[f28])).
% 1.58/0.59  fof(f28,plain,(
% 1.58/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.59    inference(cnf_transformation,[],[f17])).
% 1.58/0.59  fof(f17,plain,(
% 1.58/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.59    inference(flattening,[],[f16])).
% 1.58/0.59  fof(f16,plain,(
% 1.58/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.59    inference(nnf_transformation,[],[f1])).
% 1.58/0.59  fof(f1,axiom,(
% 1.58/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.59  fof(f37,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f24,f31])).
% 1.58/0.59  fof(f31,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f3])).
% 1.58/0.59  fof(f3,axiom,(
% 1.58/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.59  fof(f24,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f15])).
% 1.58/0.59  fof(f15,plain,(
% 1.58/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.58/0.59    inference(flattening,[],[f14])).
% 1.58/0.59  fof(f14,plain,(
% 1.58/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.58/0.59    inference(nnf_transformation,[],[f4])).
% 1.58/0.59  fof(f4,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.58/0.59  fof(f53,plain,(
% 1.58/0.59    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl3_3),
% 1.58/0.59    inference(avatar_component_clause,[],[f51])).
% 1.58/0.59  fof(f51,plain,(
% 1.58/0.59    spl3_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.58/0.59  fof(f48,plain,(
% 1.58/0.59    k1_xboole_0 != sK1 | spl3_2),
% 1.58/0.59    inference(avatar_component_clause,[],[f46])).
% 1.58/0.59  fof(f46,plain,(
% 1.58/0.59    spl3_2 <=> k1_xboole_0 = sK1),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.58/0.59  fof(f43,plain,(
% 1.58/0.59    v1_funct_1(sK2) | ~spl3_1),
% 1.58/0.59    inference(avatar_component_clause,[],[f41])).
% 1.58/0.59  fof(f41,plain,(
% 1.58/0.59    spl3_1 <=> v1_funct_1(sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.58/0.59  fof(f64,plain,(
% 1.58/0.59    spl3_5),
% 1.58/0.59    inference(avatar_split_clause,[],[f33,f61])).
% 1.58/0.59  fof(f33,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 1.58/0.59    inference(definition_unfolding,[],[f20,f32])).
% 1.58/0.59  fof(f32,plain,(
% 1.58/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f30,f31])).
% 1.58/0.59  fof(f30,plain,(
% 1.58/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f2])).
% 1.58/0.59  fof(f2,axiom,(
% 1.58/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.59  fof(f20,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.58/0.59    inference(cnf_transformation,[],[f13])).
% 1.58/0.59  fof(f13,plain,(
% 1.58/0.59    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.58/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 1.58/0.59  fof(f12,plain,(
% 1.58/0.59    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f9,plain,(
% 1.58/0.59    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.58/0.59    inference(flattening,[],[f8])).
% 1.58/0.59  % (11845)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.58/0.59  fof(f8,plain,(
% 1.58/0.59    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.58/0.59    inference(ennf_transformation,[],[f7])).
% 1.58/0.59  fof(f7,negated_conjecture,(
% 1.58/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.58/0.59    inference(negated_conjecture,[],[f6])).
% 1.58/0.59  fof(f6,conjecture,(
% 1.58/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.58/0.59  fof(f59,plain,(
% 1.58/0.59    spl3_4),
% 1.58/0.59    inference(avatar_split_clause,[],[f34,f56])).
% 1.58/0.59  fof(f34,plain,(
% 1.58/0.59    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 1.58/0.59    inference(definition_unfolding,[],[f19,f32])).
% 1.58/0.59  fof(f19,plain,(
% 1.58/0.59    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.58/0.59    inference(cnf_transformation,[],[f13])).
% 1.58/0.59  fof(f54,plain,(
% 1.58/0.59    ~spl3_3),
% 1.58/0.59    inference(avatar_split_clause,[],[f22,f51])).
% 1.58/0.59  fof(f22,plain,(
% 1.58/0.59    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.58/0.59    inference(cnf_transformation,[],[f13])).
% 1.58/0.59  fof(f49,plain,(
% 1.58/0.59    ~spl3_2),
% 1.58/0.59    inference(avatar_split_clause,[],[f21,f46])).
% 1.58/0.59  fof(f21,plain,(
% 1.58/0.59    k1_xboole_0 != sK1),
% 1.58/0.59    inference(cnf_transformation,[],[f13])).
% 1.58/0.59  fof(f44,plain,(
% 1.58/0.59    spl3_1),
% 1.58/0.59    inference(avatar_split_clause,[],[f18,f41])).
% 1.58/0.59  fof(f18,plain,(
% 1.58/0.59    v1_funct_1(sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f13])).
% 1.58/0.59  % SZS output end Proof for theBenchmark
% 1.58/0.59  % (11867)------------------------------
% 1.58/0.59  % (11867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (11867)Termination reason: Refutation
% 1.58/0.59  
% 1.58/0.59  % (11867)Memory used [KB]: 10746
% 1.58/0.59  % (11867)Time elapsed: 0.091 s
% 1.58/0.59  % (11867)------------------------------
% 1.58/0.59  % (11867)------------------------------
% 1.58/0.59  % (11845)Refutation not found, incomplete strategy% (11845)------------------------------
% 1.58/0.59  % (11845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (11845)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (11845)Memory used [KB]: 1663
% 1.58/0.59  % (11845)Time elapsed: 0.156 s
% 1.58/0.59  % (11845)------------------------------
% 1.58/0.59  % (11845)------------------------------
% 1.58/0.59  % (11869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.58/0.60  % (11848)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.58/0.60  % (11846)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.58/0.60  % (11843)Success in time 0.233 s
%------------------------------------------------------------------------------
