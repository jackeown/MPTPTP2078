%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  75 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 198 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f65,f74,f107])).

fof(f107,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f104,f78])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f75,f35,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f75,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f34,f59,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f104,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK2(sK1)),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f64,f73,f43])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK5(X0,X4),X0)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(sK4(X0,X1),X1) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK5(X0,X4))
              & r2_hidden(sK5(X0,X4),X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X0) )
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X0) )
     => ( r1_tarski(X4,sK5(X0,X4))
        & r2_hidden(sK5(X0,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f73,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_4
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f64,plain,
    ( sP0(k1_xboole_0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_3
  <=> sP0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f74,plain,
    ( spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f69,f50,f71])).

fof(f50,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f69,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f52,plain,
    ( k1_xboole_0 != sK1
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f65,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f60,f55,f62])).

fof(f55,plain,
    ( spl6_2
  <=> r1_setfam_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f60,plain,
    ( sP0(k1_xboole_0,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ~ sP0(X1,X0) )
      & ( sP0(X1,X0)
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> sP0(X1,X0) ) ),
    inference(definition_folding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f57,plain,
    ( r1_setfam_1(sK1,k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    r1_setfam_1(sK1,k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    & r1_setfam_1(sK1,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK1
      & r1_setfam_1(sK1,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f53,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (8705)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (8705)Refutation not found, incomplete strategy% (8705)------------------------------
% 0.21/0.44  % (8705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (8705)Memory used [KB]: 10490
% 0.21/0.44  % (8705)Time elapsed: 0.056 s
% 0.21/0.44  % (8705)------------------------------
% 0.21/0.44  % (8705)------------------------------
% 0.21/0.45  % (8720)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (8712)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.45  % (8720)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f53,f58,f65,f74,f107])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ~spl6_3 | ~spl6_4),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    $false | (~spl6_3 | ~spl6_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f104,f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f75,f35,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f34,f59,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f37,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    r2_hidden(sK5(k1_xboole_0,sK2(sK1)),k1_xboole_0) | (~spl6_3 | ~spl6_4)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f64,f73,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X4,X0,X1] : (r2_hidden(sK5(X0,X4),X0) | ~r2_hidden(X4,X1) | ~sP0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK4(X0,X1),X1))) & (! [X4] : ((r1_tarski(X4,sK5(X0,X4)) & r2_hidden(sK5(X0,X4),X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1)) => (! [X3] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X4,X0] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) => (r1_tarski(X4,sK5(X0,X4)) & r2_hidden(sK5(X0,X4),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~sP0(X1,X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    r2_hidden(sK2(sK1),sK1) | ~spl6_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl6_4 <=> r2_hidden(sK2(sK1),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    sP0(k1_xboole_0,sK1) | ~spl6_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl6_3 <=> sP0(k1_xboole_0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl6_4 | spl6_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f69,f50,f71])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    spl6_1 <=> k1_xboole_0 = sK1),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    r2_hidden(sK2(sK1),sK1) | spl6_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f52,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    k1_xboole_0 != sK1 | spl6_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f50])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl6_3 | ~spl6_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f60,f55,f62])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl6_2 <=> r1_setfam_1(sK1,k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    sP0(k1_xboole_0,sK1) | ~spl6_2),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f57,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (sP0(X1,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> sP0(X1,X0))),
% 0.21/0.45    inference(definition_folding,[],[f17,f18])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    r1_setfam_1(sK1,k1_xboole_0) | ~spl6_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f55])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl6_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f55])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    r1_setfam_1(sK1,k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    k1_xboole_0 != sK1 & r1_setfam_1(sK1,k1_xboole_0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK1 & r1_setfam_1(sK1,k1_xboole_0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ~spl6_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f33,f50])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    k1_xboole_0 != sK1),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (8720)------------------------------
% 0.21/0.45  % (8720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8720)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (8720)Memory used [KB]: 10618
% 0.21/0.45  % (8720)Time elapsed: 0.071 s
% 0.21/0.45  % (8720)------------------------------
% 0.21/0.45  % (8720)------------------------------
% 0.21/0.45  % (8703)Success in time 0.099 s
%------------------------------------------------------------------------------
