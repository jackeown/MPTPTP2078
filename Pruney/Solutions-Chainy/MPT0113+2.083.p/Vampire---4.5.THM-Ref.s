%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 236 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f56,f67,f74,f93,f184,f234,f297])).

fof(f297,plain,
    ( spl3_1
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f290,f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f290,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f22,f183])).

fof(f183,plain,
    ( sK0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_13
  <=> sK0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f234,plain,
    ( spl3_5
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f220,f22])).

fof(f220,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_5
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f179,f65,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f65,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_5
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f179,plain,
    ( r2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_12
  <=> r2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f184,plain,
    ( spl3_12
    | spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f173,f44,f181,f177])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f173,plain,
    ( sK0 = k4_xboole_0(sK1,sK2)
    | r2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f28,f46])).

fof(f46,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f93,plain,
    ( spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f23,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f90,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f76,f73])).

fof(f73,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_6
  <=> k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( ! [X0] : ~ r1_xboole_0(sK2,k2_xboole_0(sK0,X0))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f54,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_4
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f68,f44,f71])).

fof(f68,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f67,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f61,f35,f63])).

fof(f61,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(resolution,[],[f26,f37])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f50,f39,f52])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_2 ),
    inference(resolution,[],[f25,f41])).

fof(f41,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f42,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39,f35])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (22958)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (22959)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (22954)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (22948)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (22959)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f42,f47,f56,f67,f74,f93,f184,f234,f297])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    spl3_1 | ~spl3_13),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f296])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    $false | (spl3_1 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f290,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl3_13),
% 0.20/0.49    inference(superposition,[],[f22,f183])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK1,sK2) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    spl3_13 <=> sK0 = k4_xboole_0(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    spl3_5 | ~spl3_12),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f233])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    $false | (spl3_5 | ~spl3_12)),
% 0.20/0.49    inference(subsumption_resolution,[],[f220,f22])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | (spl3_5 | ~spl3_12)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f179,f65,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r2_xboole_0(X0,X2) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ~r2_xboole_0(sK0,sK1) | spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl3_5 <=> r2_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    r2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    spl3_12 <=> r2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl3_12 | spl3_13 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f173,f44,f181,f177])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl3_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK1,sK2) | r2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f28,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f44])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_4 | ~spl3_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    $false | (spl3_4 | ~spl3_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f90,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f23,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | (spl3_4 | ~spl3_6)),
% 0.20/0.49    inference(superposition,[],[f76,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl3_6 <=> k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_xboole_0(sK2,k2_xboole_0(sK0,X0))) ) | spl3_4),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f54,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ~r1_xboole_0(sK2,sK0) | spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_4 <=> r1_xboole_0(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_6 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f44,f71])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    k4_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f46,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~spl3_5 | spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f35,f63])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~r2_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(resolution,[],[f26,f37])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ~spl3_4 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f50,f39,f52])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~r1_xboole_0(sK2,sK0) | spl3_2),
% 0.20/0.49    inference(resolution,[],[f25,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f44])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f39,f35])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22959)------------------------------
% 0.20/0.49  % (22959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22959)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22959)Memory used [KB]: 10746
% 0.20/0.49  % (22959)Time elapsed: 0.032 s
% 0.20/0.49  % (22959)------------------------------
% 0.20/0.49  % (22959)------------------------------
% 0.20/0.49  % (22946)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (22956)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (22952)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (22942)Success in time 0.135 s
%------------------------------------------------------------------------------
