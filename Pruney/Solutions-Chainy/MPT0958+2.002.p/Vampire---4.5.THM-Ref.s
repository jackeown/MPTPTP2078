%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  73 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 ( 351 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f57,f71])).

fof(f71,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f69,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f63,f38])).

fof(f38,plain,
    ( ~ r4_relat_2(k1_wellord2(sK0),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_1
  <=> r4_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f63,plain,
    ( r4_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( sK3(k1_wellord2(sK0),sK0) != sK3(k1_wellord2(sK0),sK0)
    | r4_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f34,f56])).

fof(f56,plain,
    ( sK4(k1_wellord2(sK0),sK0) = sK3(k1_wellord2(sK0),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_2
  <=> sK4(k1_wellord2(sK0),sK0) = sK3(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != sK4(X0,X1)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ( sK3(X0,X1) != sK4(X0,X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1)
              & r2_hidden(sK3(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK3(X0,X1) != sK4(X0,X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( X2 = X3
                | ~ r2_hidden(k4_tarski(X3,X2),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

fof(f57,plain,
    ( spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f51,f36,f54])).

fof(f51,plain,
    ( sK4(k1_wellord2(sK0),sK0) = sK3(k1_wellord2(sK0),sK0)
    | spl5_1 ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r4_relat_2(k1_wellord2(X0),X1)
      | sK4(k1_wellord2(X0),X1) = sK3(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK4(k1_wellord2(X0),X1) = sK3(k1_wellord2(X0),X1)
      | r4_relat_2(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sK4(k1_wellord2(X0),X1) = sK3(k1_wellord2(X0),X1)
      | r4_relat_2(k1_wellord2(X0),X1)
      | r4_relat_2(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),sK3(k1_wellord2(X2),X3)),k1_wellord2(X2))
      | sK4(k1_wellord2(X2),X3) = sK3(k1_wellord2(X2),X3)
      | r4_relat_2(k1_wellord2(X2),X3) ) ),
    inference(subsumption_resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),sK3(k1_wellord2(X2),X3)),k1_wellord2(X2))
      | sK4(k1_wellord2(X2),X3) = sK3(k1_wellord2(X2),X3)
      | r4_relat_2(k1_wellord2(X2),X3)
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f40,f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(k4_tarski(X1,X0),k1_wellord2(X2))
      | X0 = X1
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

fof(f25,plain,(
    ! [X4,X0,X3] :
      ( ~ v4_relat_2(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK1(X0) != sK2(X0)
            & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK1(X0) != sK2(X0)
        & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f39,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    ~ r4_relat_2(k1_wellord2(sK0),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r4_relat_2(k1_wellord2(sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f12,plain,
    ( ? [X0] : ~ r4_relat_2(k1_wellord2(X0),X0)
   => ~ r4_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r4_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r4_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r4_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (22167)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (22175)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (22167)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f39,f57,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl5_1 | ~spl5_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    $false | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~v1_relat_1(k1_wellord2(sK0)) | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f63,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~r4_relat_2(k1_wellord2(sK0),sK0) | spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    spl5_1 <=> r4_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r4_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    sK3(k1_wellord2(sK0),sK0) != sK3(k1_wellord2(sK0),sK0) | r4_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_2),
% 0.20/0.49    inference(superposition,[],[f34,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    sK4(k1_wellord2(sK0),sK0) = sK3(k1_wellord2(sK0),sK0) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl5_2 <=> sK4(k1_wellord2(sK0),sK0) = sK3(k1_wellord2(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK3(X0,X1) != sK4(X0,X1) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | (sK3(X0,X1) != sK4(X0,X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) & r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK3(X0,X1) != sK4(X0,X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) & r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(rectify,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl5_2 | spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f36,f54])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    sK4(k1_wellord2(sK0),sK0) = sK3(k1_wellord2(sK0),sK0) | spl5_1),
% 0.20/0.49    inference(resolution,[],[f50,f38])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r4_relat_2(k1_wellord2(X0),X1) | sK4(k1_wellord2(X0),X1) = sK3(k1_wellord2(X0),X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f49,f24])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK4(k1_wellord2(X0),X1) = sK3(k1_wellord2(X0),X1) | r4_relat_2(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK4(k1_wellord2(X0),X1) = sK3(k1_wellord2(X0),X1) | r4_relat_2(k1_wellord2(X0),X1) | r4_relat_2(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.49    inference(resolution,[],[f46,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),sK3(k1_wellord2(X2),X3)),k1_wellord2(X2)) | sK4(k1_wellord2(X2),X3) = sK3(k1_wellord2(X2),X3) | r4_relat_2(k1_wellord2(X2),X3)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f44,f24])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK4(k1_wellord2(X2),X3),sK3(k1_wellord2(X2),X3)),k1_wellord2(X2)) | sK4(k1_wellord2(X2),X3) = sK3(k1_wellord2(X2),X3) | r4_relat_2(k1_wellord2(X2),X3) | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.20/0.49    inference(resolution,[],[f41,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X0),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | X0 = X1) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f40,f24])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(k4_tarski(X1,X0),k1_wellord2(X2)) | X0 = X1 | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.20/0.49    inference(resolution,[],[f25,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0] : (v4_relat_2(k1_wellord2(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : v4_relat_2(k1_wellord2(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X4,X0,X3] : (~v4_relat_2(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (((v4_relat_2(X0) | (sK1(X0) != sK2(X0) & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK1(X0) != sK2(X0) & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(rectify,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f36])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ~r4_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ~r4_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : ~r4_relat_2(k1_wellord2(X0),X0) => ~r4_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : ~r4_relat_2(k1_wellord2(X0),X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0] : r4_relat_2(k1_wellord2(X0),X0)),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0] : r4_relat_2(k1_wellord2(X0),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord2)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22167)------------------------------
% 0.20/0.49  % (22167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22167)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22167)Memory used [KB]: 6140
% 0.20/0.49  % (22167)Time elapsed: 0.089 s
% 0.20/0.49  % (22167)------------------------------
% 0.20/0.49  % (22167)------------------------------
% 0.20/0.49  % (22168)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (22161)Success in time 0.139 s
%------------------------------------------------------------------------------
