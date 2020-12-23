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
% DateTime   : Thu Dec  3 12:59:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 282 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  349 (1214 expanded)
%              Number of equality atoms :  149 ( 604 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f141,f144,f147,f166,f189,f238,f258,f260,f273,f276,f284])).

fof(f284,plain,(
    ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f134,f269])).

fof(f269,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_27
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f134,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f33,f63])).

% (15217)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (15227)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (15231)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (15218)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (15210)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (15228)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (15214)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (15230)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (15215)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (15225)Refutation not found, incomplete strategy% (15225)------------------------------
% (15225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15225)Termination reason: Refutation not found, incomplete strategy

% (15225)Memory used [KB]: 1663
% (15225)Time elapsed: 0.137 s
% (15225)------------------------------
% (15225)------------------------------
% (15211)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (15219)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (15221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (15219)Refutation not found, incomplete strategy% (15219)------------------------------
% (15219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15219)Termination reason: Refutation not found, incomplete strategy

% (15219)Memory used [KB]: 10618
% (15219)Time elapsed: 0.150 s
% (15219)------------------------------
% (15219)------------------------------
% (15223)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f63,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(global_subsumption,[],[f30,f31,f32,f59])).

fof(f59,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f51,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

% (15222)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f51,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f28,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f276,plain,
    ( ~ spl7_1
    | spl7_28 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl7_1
    | spl7_28 ),
    inference(subsumption_resolution,[],[f192,f274])).

fof(f274,plain,
    ( ~ r2_hidden(k2_mcart_1(sK4),sK2)
    | spl7_28 ),
    inference(resolution,[],[f272,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f272,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl7_28
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f192,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f66,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f273,plain,
    ( spl7_27
    | ~ spl7_28
    | ~ spl7_1
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f266,f236,f65,f271,f268])).

fof(f236,plain,
    ( spl7_24
  <=> ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2)
        | sK3 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f266,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4)
    | ~ spl7_1
    | ~ spl7_24 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | sK3 = k2_mcart_1(sK4)
    | ~ spl7_1
    | ~ spl7_24 ),
    inference(superposition,[],[f237,f223])).

fof(f223,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f213,f199])).

fof(f199,plain,
    ( k2_mcart_1(sK4) = sK6(sK4)
    | ~ spl7_1 ),
    inference(superposition,[],[f36,f190])).

fof(f190,plain,
    ( sK4 = k4_tarski(sK5(sK4),sK6(sK4))
    | ~ spl7_1 ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK5(X0),sK6(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f21,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f213,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),sK6(sK4))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f190,f198])).

fof(f198,plain,
    ( k1_mcart_1(sK4) = sK5(sK4)
    | ~ spl7_1 ),
    inference(superposition,[],[f35,f190])).

fof(f35,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f237,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | ~ m1_subset_1(X0,sK2)
        | sK3 = X0 )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f236])).

fof(f260,plain,
    ( ~ spl7_1
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl7_1
    | spl7_23 ),
    inference(subsumption_resolution,[],[f196,f253])).

fof(f253,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_1
    | spl7_23 ),
    inference(resolution,[],[f251,f38])).

% (15223)Refutation not found, incomplete strategy% (15223)------------------------------
% (15223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15223)Termination reason: Refutation not found, incomplete strategy

% (15223)Memory used [KB]: 1663
% (15223)Time elapsed: 0.149 s
% (15223)------------------------------
% (15223)------------------------------
fof(f251,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_1
    | spl7_23 ),
    inference(backward_demodulation,[],[f234,f228])).

fof(f228,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(superposition,[],[f36,f194])).

fof(f194,plain,
    ( k1_mcart_1(sK4) = k4_tarski(sK5(k1_mcart_1(sK4)),sK6(k1_mcart_1(sK4)))
    | ~ spl7_1 ),
    inference(resolution,[],[f191,f49])).

fof(f191,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_1 ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f234,plain,
    ( ~ m1_subset_1(sK6(k1_mcart_1(sK4)),sK1)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_23
  <=> m1_subset_1(sK6(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f196,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f191,f45])).

fof(f258,plain,
    ( ~ spl7_1
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl7_1
    | spl7_22 ),
    inference(subsumption_resolution,[],[f195,f250])).

fof(f250,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl7_1
    | spl7_22 ),
    inference(resolution,[],[f241,f38])).

fof(f241,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl7_1
    | spl7_22 ),
    inference(backward_demodulation,[],[f231,f227])).

fof(f227,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = sK5(k1_mcart_1(sK4))
    | ~ spl7_1 ),
    inference(superposition,[],[f35,f194])).

fof(f231,plain,
    ( ~ m1_subset_1(sK5(k1_mcart_1(sK4)),sK0)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl7_22
  <=> m1_subset_1(sK5(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f195,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f191,f44])).

fof(f238,plain,
    ( ~ spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f226,f65,f236,f233,f230])).

fof(f226,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(sK6(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(sK5(k1_mcart_1(sK4)),sK0) )
    | ~ spl7_1 ),
    inference(superposition,[],[f50,f194])).

fof(f50,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f29,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f189,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f185,f68,f65])).

fof(f68,plain,
    ( spl7_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f185,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f166,plain,
    ( spl7_4
    | spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f164,f107,f86,f89])).

fof(f89,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f86,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f107,plain,
    ( spl7_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f164,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl7_9 ),
    inference(superposition,[],[f39,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f147,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f31,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f144,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f30,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f141,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f32,f93])).

fof(f93,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f109,plain,
    ( spl7_5
    | spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f84,f68,f107,f92])).

fof(f84,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl7_2 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl7_2 ),
    inference(superposition,[],[f39,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f69,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:53:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.48  % (15224)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.48  % (15216)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.49  % (15208)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (15224)Refutation not found, incomplete strategy% (15224)------------------------------
% 0.20/0.49  % (15224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15224)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15224)Memory used [KB]: 10746
% 0.20/0.49  % (15224)Time elapsed: 0.051 s
% 0.20/0.49  % (15224)------------------------------
% 0.20/0.49  % (15224)------------------------------
% 0.20/0.51  % (15212)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (15206)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (15205)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (15204)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (15220)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (15202)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (15203)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (15225)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (15207)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (15229)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (15226)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (15201)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (15213)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (15201)Refutation not found, incomplete strategy% (15201)------------------------------
% 0.20/0.53  % (15201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15201)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15201)Memory used [KB]: 1663
% 0.20/0.53  % (15201)Time elapsed: 0.125 s
% 0.20/0.53  % (15201)------------------------------
% 0.20/0.53  % (15201)------------------------------
% 0.20/0.53  % (15203)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f109,f141,f144,f147,f166,f189,f238,f258,f260,f273,f276,f284])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    ~spl7_27),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f277])).
% 0.20/0.53  fof(f277,plain,(
% 0.20/0.53    $false | ~spl7_27),
% 0.20/0.53    inference(subsumption_resolution,[],[f134,f269])).
% 0.20/0.53  fof(f269,plain,(
% 0.20/0.53    sK3 = k2_mcart_1(sK4) | ~spl7_27),
% 0.20/0.53    inference(avatar_component_clause,[],[f268])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    spl7_27 <=> sK3 = k2_mcart_1(sK4)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    sK3 != k2_mcart_1(sK4)),
% 0.20/0.53    inference(superposition,[],[f33,f63])).
% 0.20/0.53  % (15217)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (15227)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (15231)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (15218)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (15210)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (15228)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (15214)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (15230)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (15215)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (15225)Refutation not found, incomplete strategy% (15225)------------------------------
% 0.20/0.54  % (15225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15225)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15225)Memory used [KB]: 1663
% 0.20/0.54  % (15225)Time elapsed: 0.137 s
% 0.20/0.54  % (15225)------------------------------
% 0.20/0.54  % (15225)------------------------------
% 0.20/0.54  % (15211)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (15219)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (15221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (15219)Refutation not found, incomplete strategy% (15219)------------------------------
% 0.20/0.54  % (15219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15219)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15219)Memory used [KB]: 10618
% 0.20/0.54  % (15219)Time elapsed: 0.150 s
% 0.20/0.54  % (15219)------------------------------
% 0.20/0.54  % (15219)------------------------------
% 0.20/0.54  % (15223)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.54    inference(global_subsumption,[],[f30,f31,f32,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.54    inference(resolution,[],[f51,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f48,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.54  % (15222)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    inference(definition_unfolding,[],[f28,f43])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f11])).
% 0.20/0.54  fof(f11,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    k1_xboole_0 != sK2),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    k1_xboole_0 != sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    ~spl7_1 | spl7_28),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f275])).
% 0.20/0.54  fof(f275,plain,(
% 0.20/0.54    $false | (~spl7_1 | spl7_28)),
% 0.20/0.54    inference(subsumption_resolution,[],[f192,f274])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    ~r2_hidden(k2_mcart_1(sK4),sK2) | spl7_28),
% 0.20/0.54    inference(resolution,[],[f272,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.54  fof(f272,plain,(
% 0.20/0.54    ~m1_subset_1(k2_mcart_1(sK4),sK2) | spl7_28),
% 0.20/0.54    inference(avatar_component_clause,[],[f271])).
% 0.20/0.54  fof(f271,plain,(
% 0.20/0.54    spl7_28 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl7_1),
% 0.20/0.54    inference(resolution,[],[f66,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    spl7_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.54  fof(f273,plain,(
% 0.20/0.54    spl7_27 | ~spl7_28 | ~spl7_1 | ~spl7_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f266,f236,f65,f271,f268])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    spl7_24 <=> ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2) | sK3 = X0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    ~m1_subset_1(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | (~spl7_1 | ~spl7_24)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f265])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    sK4 != sK4 | ~m1_subset_1(k2_mcart_1(sK4),sK2) | sK3 = k2_mcart_1(sK4) | (~spl7_1 | ~spl7_24)),
% 0.20/0.55    inference(superposition,[],[f237,f223])).
% 0.20/0.55  fof(f223,plain,(
% 0.20/0.55    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl7_1),
% 0.20/0.55    inference(backward_demodulation,[],[f213,f199])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    k2_mcart_1(sK4) = sK6(sK4) | ~spl7_1),
% 0.20/0.55    inference(superposition,[],[f36,f190])).
% 0.20/0.55  fof(f190,plain,(
% 0.20/0.55    sK4 = k4_tarski(sK5(sK4),sK6(sK4)) | ~spl7_1),
% 0.20/0.55    inference(resolution,[],[f66,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k4_tarski(sK5(X0),sK6(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f21,f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK5(X0),sK6(X0)) = X0)),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.55  fof(f213,plain,(
% 0.20/0.55    sK4 = k4_tarski(k1_mcart_1(sK4),sK6(sK4)) | ~spl7_1),
% 0.20/0.55    inference(backward_demodulation,[],[f190,f198])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    k1_mcart_1(sK4) = sK5(sK4) | ~spl7_1),
% 0.20/0.55    inference(superposition,[],[f35,f190])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2) | sK3 = X0) ) | ~spl7_24),
% 0.20/0.55    inference(avatar_component_clause,[],[f236])).
% 0.20/0.55  fof(f260,plain,(
% 0.20/0.55    ~spl7_1 | spl7_23),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f259])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    $false | (~spl7_1 | spl7_23)),
% 0.20/0.55    inference(subsumption_resolution,[],[f196,f253])).
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | (~spl7_1 | spl7_23)),
% 0.20/0.55    inference(resolution,[],[f251,f38])).
% 0.20/0.55  % (15223)Refutation not found, incomplete strategy% (15223)------------------------------
% 0.20/0.55  % (15223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15223)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15223)Memory used [KB]: 1663
% 0.20/0.55  % (15223)Time elapsed: 0.149 s
% 0.20/0.55  % (15223)------------------------------
% 0.20/0.55  % (15223)------------------------------
% 0.20/0.55  fof(f251,plain,(
% 0.20/0.55    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | (~spl7_1 | spl7_23)),
% 0.20/0.55    inference(backward_demodulation,[],[f234,f228])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    k2_mcart_1(k1_mcart_1(sK4)) = sK6(k1_mcart_1(sK4)) | ~spl7_1),
% 0.20/0.55    inference(superposition,[],[f36,f194])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    k1_mcart_1(sK4) = k4_tarski(sK5(k1_mcart_1(sK4)),sK6(k1_mcart_1(sK4))) | ~spl7_1),
% 0.20/0.55    inference(resolution,[],[f191,f49])).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl7_1),
% 0.20/0.55    inference(resolution,[],[f66,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    ~m1_subset_1(sK6(k1_mcart_1(sK4)),sK1) | spl7_23),
% 0.20/0.55    inference(avatar_component_clause,[],[f233])).
% 0.20/0.55  fof(f233,plain,(
% 0.20/0.55    spl7_23 <=> m1_subset_1(sK6(k1_mcart_1(sK4)),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl7_1),
% 0.20/0.55    inference(resolution,[],[f191,f45])).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    ~spl7_1 | spl7_22),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f257])).
% 0.20/0.55  fof(f257,plain,(
% 0.20/0.55    $false | (~spl7_1 | spl7_22)),
% 0.20/0.55    inference(subsumption_resolution,[],[f195,f250])).
% 0.20/0.55  fof(f250,plain,(
% 0.20/0.55    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | (~spl7_1 | spl7_22)),
% 0.20/0.55    inference(resolution,[],[f241,f38])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | (~spl7_1 | spl7_22)),
% 0.20/0.55    inference(backward_demodulation,[],[f231,f227])).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    k1_mcart_1(k1_mcart_1(sK4)) = sK5(k1_mcart_1(sK4)) | ~spl7_1),
% 0.20/0.55    inference(superposition,[],[f35,f194])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    ~m1_subset_1(sK5(k1_mcart_1(sK4)),sK0) | spl7_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f230])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    spl7_22 <=> m1_subset_1(sK5(k1_mcart_1(sK4)),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl7_1),
% 0.20/0.55    inference(resolution,[],[f191,f44])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ~spl7_22 | ~spl7_23 | spl7_24 | ~spl7_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f226,f65,f236,f233,f230])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2) | ~m1_subset_1(sK6(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK5(k1_mcart_1(sK4)),sK0)) ) | ~spl7_1),
% 0.20/0.55    inference(superposition,[],[f50,f194])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f29,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    spl7_1 | spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f185,f68,f65])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    spl7_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.55    inference(resolution,[],[f51,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    spl7_4 | spl7_3 | ~spl7_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f164,f107,f86,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    spl7_4 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    spl7_3 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    spl7_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl7_9),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f157])).
% 0.20/0.55  fof(f157,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl7_9),
% 0.20/0.55    inference(superposition,[],[f39,f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl7_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f107])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f147,plain,(
% 0.20/0.55    ~spl7_4),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    $false | ~spl7_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f31,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl7_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f89])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ~spl7_3),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    $false | ~spl7_3),
% 0.20/0.55    inference(subsumption_resolution,[],[f30,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl7_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f86])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    ~spl7_5),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    $false | ~spl7_5),
% 0.20/0.55    inference(subsumption_resolution,[],[f32,f93])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl7_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f92])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    spl7_5 <=> k1_xboole_0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl7_5 | spl7_9 | ~spl7_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f84,f68,f107,f92])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl7_2),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl7_2),
% 0.20/0.55    inference(superposition,[],[f39,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_2),
% 0.20/0.55    inference(resolution,[],[f69,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f68])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (15203)------------------------------
% 0.20/0.55  % (15203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15203)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (15203)Memory used [KB]: 10874
% 0.20/0.55  % (15203)Time elapsed: 0.133 s
% 0.20/0.55  % (15203)------------------------------
% 0.20/0.55  % (15203)------------------------------
% 0.20/0.55  % (15222)Refutation not found, incomplete strategy% (15222)------------------------------
% 0.20/0.55  % (15222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15222)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15222)Memory used [KB]: 10746
% 0.20/0.55  % (15222)Time elapsed: 0.152 s
% 0.20/0.55  % (15222)------------------------------
% 0.20/0.55  % (15222)------------------------------
% 0.20/0.55  % (15195)Success in time 0.196 s
%------------------------------------------------------------------------------
