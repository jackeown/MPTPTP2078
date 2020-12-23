%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 351 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f70,f95,f105,f115,f138])).

fof(f138,plain,
    ( ~ spl3_2
    | spl3_5
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl3_2
    | spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f134,f119])).

fof(f119,plain,
    ( r2_hidden(sK2(sK0,sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f114,f25])).

fof(f25,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK0 != sK1
      & ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f114,plain,
    ( m1_subset_1(sK2(sK0,sK0,sK1),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_7
  <=> m1_subset_1(sK2(sK0,sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f134,plain,
    ( ~ r2_hidden(sK2(sK0,sK0,sK1),sK1)
    | ~ spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f44,f53,f104,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK2(X0,X1,X2),X2)
            & r2_hidden(sK2(X0,X1,X2),X1)
            & m1_subset_1(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f104,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_5
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f30,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f115,plain,
    ( spl3_7
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f100,f92,f51,f46,f112])).

fof(f46,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f92,plain,
    ( spl3_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f100,plain,
    ( m1_subset_1(sK2(sK0,sK0,sK1),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f87,f97])).

fof(f97,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f48,f94,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f94,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f48,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f87,plain,
    ( m1_subset_1(sK2(sK0,sK0,sK1),sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | m1_subset_1(sK2(X1,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f36,f44])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f97,f92,f46,f102])).

fof(f95,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f75,f67,f92])).

fof(f67,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f75,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f72,f29])).

fof(f29,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

% (17424)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f72,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f69,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f51,f67])).

fof(f56,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f27,f53,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f27,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (17446)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.47  % (17434)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (17434)Refutation not found, incomplete strategy% (17434)------------------------------
% 0.21/0.47  % (17434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (17434)Memory used [KB]: 10490
% 0.21/0.47  % (17434)Time elapsed: 0.064 s
% 0.21/0.47  % (17434)------------------------------
% 0.21/0.47  % (17434)------------------------------
% 0.21/0.48  % (17446)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f49,f54,f70,f95,f105,f115,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~spl3_2 | spl3_5 | ~spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    $false | (~spl3_2 | spl3_5 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,sK1),sK1) | ~spl3_7),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f114,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK0,sK1),sK0) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl3_7 <=> m1_subset_1(sK2(sK0,sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,sK0,sK1),sK1) | (~spl3_2 | spl3_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f44,f53,f104,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl3_5 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f30,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl3_7 | spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f100,f92,f51,f46,f112])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl3_1 <=> sK0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl3_4 <=> r1_tarski(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK0,sK1),sK0) | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | (spl3_1 | ~spl3_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f48,f94,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    sK0 != sK1 | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK0,sK1),sK0) | r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f63,f53])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X1,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f36,f44])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~spl3_5 | spl3_1 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f92,f46,f102])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_4 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f75,f67,f92])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.21/0.48    inference(forward_demodulation,[],[f72,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.48  % (17424)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f69,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl3_3 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f51,f67])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f53,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f51])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f46])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    sK0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17446)------------------------------
% 0.21/0.48  % (17446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17446)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17446)Memory used [KB]: 10618
% 0.21/0.48  % (17446)Time elapsed: 0.070 s
% 0.21/0.48  % (17446)------------------------------
% 0.21/0.48  % (17446)------------------------------
% 0.21/0.48  % (17422)Success in time 0.123 s
%------------------------------------------------------------------------------
