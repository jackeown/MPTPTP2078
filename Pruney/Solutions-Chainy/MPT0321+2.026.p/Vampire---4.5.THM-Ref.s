%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:33 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 274 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  383 (1050 expanded)
%              Number of equality atoms :   72 ( 383 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1040,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f263,f353,f410,f416,f435,f459,f477,f480,f599,f603,f614,f649,f1029])).

fof(f1029,plain,(
    ~ spl9_29 ),
    inference(avatar_contradiction_clause,[],[f997])).

fof(f997,plain,
    ( $false
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f44,f996])).

fof(f996,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_29 ),
    inference(resolution,[],[f736,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f736,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl9_29 ),
    inference(resolution,[],[f731,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f731,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,X1),X1)
        | sK0 = X1 )
    | ~ spl9_29 ),
    inference(backward_demodulation,[],[f655,f694])).

fof(f694,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl9_29 ),
    inference(resolution,[],[f655,f356])).

fof(f356,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl9_29
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f655,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,X1),X1)
        | k3_tarski(sK0) = X1 )
    | ~ spl9_29 ),
    inference(resolution,[],[f356,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK5(X0,X1),X3) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ( r2_hidden(sK6(X0,X1),X0)
              & r2_hidden(sK5(X0,X1),sK6(X0,X1)) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK7(X0,X5),X0)
                & r2_hidden(X5,sK7(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK5(X0,X1),X3) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK5(X0,X1),X4) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f649,plain,
    ( spl9_28
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f330,f640])).

% (21307)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f640,plain,
    ( r1_tarski(sK1,sK3)
    | spl9_28
    | ~ spl9_30 ),
    inference(resolution,[],[f523,f623])).

fof(f623,plain,
    ( r2_hidden(sK4(sK1,sK3),sK1)
    | spl9_28 ),
    inference(resolution,[],[f330,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f523,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(X2,sK3),sK1)
        | r1_tarski(X2,sK3) )
    | ~ spl9_30 ),
    inference(resolution,[],[f359,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f359,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl9_30
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f330,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl9_28 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl9_28
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f614,plain,
    ( spl9_27
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f613,f222,f320])).

fof(f320,plain,
    ( spl9_27
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f222,plain,
    ( spl9_22
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f613,plain,
    ( ~ r1_tarski(sK0,sK2)
    | r1_tarski(sK3,sK1) ),
    inference(global_subsumption,[],[f373])).

fof(f373,plain,
    ( ~ r1_tarski(sK0,sK2)
    | r1_tarski(sK3,sK1) ),
    inference(global_subsumption,[],[f44,f303])).

fof(f303,plain,
    ( ~ r1_tarski(sK0,sK2)
    | r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f85,f68])).

% (21288)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (21285)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f85,plain,(
    ! [X1] :
      ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X1,sK2) ) ),
    inference(superposition,[],[f65,f43])).

fof(f43,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f603,plain,
    ( spl9_20
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f602,f329,f211])).

fof(f211,plain,
    ( spl9_20
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f602,plain,
    ( ~ r1_tarski(sK1,sK3)
    | r1_tarski(sK2,sK0) ),
    inference(global_subsumption,[],[f45,f472])).

fof(f472,plain,
    ( ~ r1_tarski(sK1,sK3)
    | r1_tarski(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f87,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    ! [X3] :
      ( r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X3,sK3) ) ),
    inference(superposition,[],[f66,f43])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f599,plain,
    ( ~ spl9_18
    | spl9_22 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | ~ spl9_18
    | spl9_22 ),
    inference(subsumption_resolution,[],[f223,f584])).

fof(f584,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl9_18
    | spl9_22 ),
    inference(resolution,[],[f515,f417])).

fof(f417,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | spl9_22 ),
    inference(resolution,[],[f223,f55])).

fof(f515,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(X2,sK2),sK0)
        | r1_tarski(X2,sK2) )
    | ~ spl9_18 ),
    inference(resolution,[],[f197,f56])).

fof(f197,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl9_18
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f223,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f480,plain,
    ( spl9_29
    | spl9_30 ),
    inference(avatar_split_clause,[],[f479,f358,f355])).

fof(f479,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f93,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f93,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X11,sK3) ) ),
    inference(superposition,[],[f70,f43])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f477,plain,
    ( spl9_17
    | spl9_18 ),
    inference(avatar_split_clause,[],[f476,f196,f193])).

fof(f193,plain,
    ( spl9_17
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f476,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f92,f71])).

fof(f92,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X8,sK2) ) ),
    inference(superposition,[],[f69,f43])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f459,plain,
    ( ~ spl9_19
    | spl9_11
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f458,f219,f151,f208])).

fof(f208,plain,
    ( spl9_19
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f151,plain,
    ( spl9_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f219,plain,
    ( spl9_21
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f458,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl9_21 ),
    inference(resolution,[],[f220,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f220,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f219])).

fof(f435,plain,(
    ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f45,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f416,plain,
    ( ~ spl9_28
    | spl9_2
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f402,f320,f81,f329])).

fof(f81,plain,
    ( spl9_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f402,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK1,sK3)
    | ~ spl9_27 ),
    inference(resolution,[],[f371,f52])).

fof(f371,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f320])).

fof(f410,plain,
    ( ~ spl9_20
    | spl9_1
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f377,f222,f78,f211])).

fof(f78,plain,
    ( spl9_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f377,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK2,sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f230,f52])).

fof(f230,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f353,plain,
    ( ~ spl9_17
    | spl9_19 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl9_17
    | spl9_19 ),
    inference(resolution,[],[f253,f194])).

fof(f194,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f253,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | spl9_19 ),
    inference(resolution,[],[f238,f55])).

fof(f238,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f263,plain,(
    spl9_21 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl9_21 ),
    inference(subsumption_resolution,[],[f47,f260])).

fof(f260,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl9_21 ),
    inference(resolution,[],[f242,f49])).

fof(f242,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK1),k1_xboole_0)
    | spl9_21 ),
    inference(resolution,[],[f231,f55])).

fof(f231,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl9_21 ),
    inference(avatar_component_clause,[],[f219])).

fof(f83,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f46,f81,f78])).

fof(f46,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.18/0.52  % (21298)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.18/0.52  % (21289)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.52  % (21290)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.53  % (21280)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (21283)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.54  % (21300)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (21279)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (21303)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (21301)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (21278)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (21292)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (21299)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (21282)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.55  % (21295)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (21302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (21304)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.55  % (21281)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.55  % (21295)Refutation not found, incomplete strategy% (21295)------------------------------
% 1.36/0.55  % (21295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (21295)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (21295)Memory used [KB]: 10618
% 1.36/0.55  % (21295)Time elapsed: 0.149 s
% 1.36/0.55  % (21295)------------------------------
% 1.36/0.55  % (21295)------------------------------
% 1.36/0.55  % (21306)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (21286)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (21284)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.56  % (21293)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.56  % (21297)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.56  % (21296)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  % (21294)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.57  % (21287)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.57  % (21291)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.57  % (21304)Refutation not found, incomplete strategy% (21304)------------------------------
% 1.36/0.57  % (21304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (21304)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (21304)Memory used [KB]: 10746
% 1.36/0.57  % (21304)Time elapsed: 0.167 s
% 1.36/0.57  % (21304)------------------------------
% 1.36/0.57  % (21304)------------------------------
% 1.36/0.58  % (21305)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.58  % (21280)Refutation found. Thanks to Tanya!
% 1.36/0.58  % SZS status Theorem for theBenchmark
% 1.36/0.58  % SZS output start Proof for theBenchmark
% 1.36/0.58  fof(f1040,plain,(
% 1.36/0.58    $false),
% 1.36/0.58    inference(avatar_sat_refutation,[],[f83,f263,f353,f410,f416,f435,f459,f477,f480,f599,f603,f614,f649,f1029])).
% 1.36/0.58  fof(f1029,plain,(
% 1.36/0.58    ~spl9_29),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f997])).
% 1.36/0.58  fof(f997,plain,(
% 1.36/0.58    $false | ~spl9_29),
% 1.36/0.58    inference(subsumption_resolution,[],[f44,f996])).
% 1.36/0.58  fof(f996,plain,(
% 1.36/0.58    k1_xboole_0 = sK0 | ~spl9_29),
% 1.36/0.58    inference(resolution,[],[f736,f47])).
% 1.36/0.58  fof(f47,plain,(
% 1.36/0.58    v1_xboole_0(k1_xboole_0)),
% 1.36/0.58    inference(cnf_transformation,[],[f4])).
% 1.36/0.58  fof(f4,axiom,(
% 1.36/0.58    v1_xboole_0(k1_xboole_0)),
% 1.36/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.36/0.58  fof(f736,plain,(
% 1.36/0.58    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) ) | ~spl9_29),
% 1.36/0.58    inference(resolution,[],[f731,f49])).
% 1.36/0.58  fof(f49,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f18])).
% 1.36/0.58  fof(f18,plain,(
% 1.36/0.58    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.36/0.58    inference(ennf_transformation,[],[f15])).
% 1.36/0.58  fof(f15,plain,(
% 1.36/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.58    inference(unused_predicate_definition_removal,[],[f1])).
% 1.36/0.58  fof(f1,axiom,(
% 1.36/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.58  fof(f731,plain,(
% 1.36/0.58    ( ! [X1] : (r2_hidden(sK5(sK0,X1),X1) | sK0 = X1) ) | ~spl9_29),
% 1.36/0.58    inference(backward_demodulation,[],[f655,f694])).
% 1.36/0.58  fof(f694,plain,(
% 1.36/0.58    sK0 = k3_tarski(sK0) | ~spl9_29),
% 1.36/0.58    inference(resolution,[],[f655,f356])).
% 1.36/0.58  fof(f356,plain,(
% 1.36/0.58    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl9_29),
% 1.36/0.58    inference(avatar_component_clause,[],[f355])).
% 1.36/0.58  fof(f355,plain,(
% 1.36/0.58    spl9_29 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.36/0.58  fof(f655,plain,(
% 1.36/0.58    ( ! [X1] : (r2_hidden(sK5(sK0,X1),X1) | k3_tarski(sK0) = X1) ) | ~spl9_29),
% 1.36/0.58    inference(resolution,[],[f356,f61])).
% 1.36/0.58  fof(f61,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 1.36/0.58    inference(cnf_transformation,[],[f38])).
% 1.36/0.58  fof(f38,plain,(
% 1.36/0.58    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f37,f36,f35])).
% 1.36/0.58  fof(f35,plain,(
% 1.36/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f36,plain,(
% 1.36/0.58    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f37,plain,(
% 1.36/0.58    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f34,plain,(
% 1.36/0.58    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.36/0.58    inference(rectify,[],[f33])).
% 1.36/0.58  fof(f33,plain,(
% 1.36/0.58    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 1.36/0.58    inference(nnf_transformation,[],[f7])).
% 1.36/0.58  fof(f7,axiom,(
% 1.36/0.58    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.36/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.36/0.58  fof(f44,plain,(
% 1.36/0.58    k1_xboole_0 != sK0),
% 1.36/0.58    inference(cnf_transformation,[],[f26])).
% 1.36/0.58  fof(f26,plain,(
% 1.36/0.58    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).
% 1.36/0.58  fof(f25,plain,(
% 1.36/0.58    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f17,plain,(
% 1.36/0.58    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.36/0.58    inference(flattening,[],[f16])).
% 1.36/0.58  fof(f16,plain,(
% 1.36/0.58    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.36/0.58    inference(ennf_transformation,[],[f13])).
% 1.36/0.58  fof(f13,negated_conjecture,(
% 1.36/0.58    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.58    inference(negated_conjecture,[],[f12])).
% 1.36/0.58  fof(f12,conjecture,(
% 1.36/0.58    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.36/0.58  fof(f649,plain,(
% 1.36/0.58    spl9_28 | ~spl9_30),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f646])).
% 1.36/0.58  fof(f646,plain,(
% 1.36/0.58    $false | (spl9_28 | ~spl9_30)),
% 1.36/0.58    inference(subsumption_resolution,[],[f330,f640])).
% 1.36/0.58  % (21307)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.58  fof(f640,plain,(
% 1.36/0.58    r1_tarski(sK1,sK3) | (spl9_28 | ~spl9_30)),
% 1.36/0.58    inference(resolution,[],[f523,f623])).
% 1.36/0.58  fof(f623,plain,(
% 1.36/0.58    r2_hidden(sK4(sK1,sK3),sK1) | spl9_28),
% 1.36/0.58    inference(resolution,[],[f330,f55])).
% 1.36/0.58  fof(f55,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f32])).
% 1.36/0.58  fof(f32,plain,(
% 1.36/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.36/0.58  fof(f31,plain,(
% 1.36/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f30,plain,(
% 1.36/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.58    inference(rectify,[],[f29])).
% 1.36/0.58  fof(f29,plain,(
% 1.36/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.58    inference(nnf_transformation,[],[f21])).
% 1.36/0.58  fof(f21,plain,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f2])).
% 1.36/0.58  fof(f2,axiom,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.58  fof(f523,plain,(
% 1.36/0.58    ( ! [X2] : (~r2_hidden(sK4(X2,sK3),sK1) | r1_tarski(X2,sK3)) ) | ~spl9_30),
% 1.36/0.58    inference(resolution,[],[f359,f56])).
% 1.36/0.58  fof(f56,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f32])).
% 1.36/0.58  fof(f359,plain,(
% 1.36/0.58    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl9_30),
% 1.36/0.58    inference(avatar_component_clause,[],[f358])).
% 1.36/0.58  fof(f358,plain,(
% 1.36/0.58    spl9_30 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.36/0.58  fof(f330,plain,(
% 1.36/0.58    ~r1_tarski(sK1,sK3) | spl9_28),
% 1.36/0.58    inference(avatar_component_clause,[],[f329])).
% 1.36/0.58  fof(f329,plain,(
% 1.36/0.58    spl9_28 <=> r1_tarski(sK1,sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.36/0.58  fof(f614,plain,(
% 1.36/0.58    spl9_27 | ~spl9_22),
% 1.36/0.58    inference(avatar_split_clause,[],[f613,f222,f320])).
% 1.36/0.58  fof(f320,plain,(
% 1.36/0.58    spl9_27 <=> r1_tarski(sK3,sK1)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 1.36/0.58  fof(f222,plain,(
% 1.36/0.58    spl9_22 <=> r1_tarski(sK0,sK2)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 1.36/0.58  fof(f613,plain,(
% 1.36/0.58    ~r1_tarski(sK0,sK2) | r1_tarski(sK3,sK1)),
% 1.36/0.58    inference(global_subsumption,[],[f373])).
% 1.36/0.58  fof(f373,plain,(
% 1.36/0.58    ~r1_tarski(sK0,sK2) | r1_tarski(sK3,sK1)),
% 1.36/0.58    inference(global_subsumption,[],[f44,f303])).
% 1.36/0.58  fof(f303,plain,(
% 1.36/0.58    ~r1_tarski(sK0,sK2) | r1_tarski(sK3,sK1) | k1_xboole_0 = sK0),
% 1.36/0.58    inference(resolution,[],[f85,f68])).
% 1.36/0.59  % (21288)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.59  % (21285)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.59  fof(f68,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f24])).
% 1.36/0.59  fof(f24,plain,(
% 1.36/0.59    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.36/0.59    inference(ennf_transformation,[],[f9])).
% 1.36/0.59  fof(f9,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.36/0.59  fof(f85,plain,(
% 1.36/0.59    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X1,sK2)) )),
% 1.36/0.59    inference(superposition,[],[f65,f43])).
% 1.36/0.59  fof(f43,plain,(
% 1.36/0.59    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.36/0.59    inference(cnf_transformation,[],[f26])).
% 1.36/0.59  fof(f65,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f23])).
% 1.36/0.59  fof(f23,plain,(
% 1.36/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f10])).
% 1.36/0.59  fof(f10,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.36/0.59  fof(f603,plain,(
% 1.36/0.59    spl9_20 | ~spl9_28),
% 1.36/0.59    inference(avatar_split_clause,[],[f602,f329,f211])).
% 1.36/0.59  fof(f211,plain,(
% 1.36/0.59    spl9_20 <=> r1_tarski(sK2,sK0)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.36/0.59  fof(f602,plain,(
% 1.36/0.59    ~r1_tarski(sK1,sK3) | r1_tarski(sK2,sK0)),
% 1.36/0.59    inference(global_subsumption,[],[f45,f472])).
% 1.36/0.59  fof(f472,plain,(
% 1.36/0.59    ~r1_tarski(sK1,sK3) | r1_tarski(sK2,sK0) | k1_xboole_0 = sK1),
% 1.36/0.59    inference(resolution,[],[f87,f67])).
% 1.36/0.59  fof(f67,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f24])).
% 1.36/0.59  fof(f87,plain,(
% 1.36/0.59    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK3)) )),
% 1.36/0.59    inference(superposition,[],[f66,f43])).
% 1.36/0.59  fof(f66,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f23])).
% 1.36/0.59  fof(f45,plain,(
% 1.36/0.59    k1_xboole_0 != sK1),
% 1.36/0.59    inference(cnf_transformation,[],[f26])).
% 1.36/0.59  fof(f599,plain,(
% 1.36/0.59    ~spl9_18 | spl9_22),
% 1.36/0.59    inference(avatar_contradiction_clause,[],[f596])).
% 1.36/0.59  fof(f596,plain,(
% 1.36/0.59    $false | (~spl9_18 | spl9_22)),
% 1.36/0.59    inference(subsumption_resolution,[],[f223,f584])).
% 1.36/0.59  fof(f584,plain,(
% 1.36/0.59    r1_tarski(sK0,sK2) | (~spl9_18 | spl9_22)),
% 1.36/0.59    inference(resolution,[],[f515,f417])).
% 1.36/0.59  fof(f417,plain,(
% 1.36/0.59    r2_hidden(sK4(sK0,sK2),sK0) | spl9_22),
% 1.36/0.59    inference(resolution,[],[f223,f55])).
% 1.36/0.59  fof(f515,plain,(
% 1.36/0.59    ( ! [X2] : (~r2_hidden(sK4(X2,sK2),sK0) | r1_tarski(X2,sK2)) ) | ~spl9_18),
% 1.36/0.59    inference(resolution,[],[f197,f56])).
% 1.36/0.59  fof(f197,plain,(
% 1.36/0.59    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl9_18),
% 1.36/0.59    inference(avatar_component_clause,[],[f196])).
% 1.36/0.59  fof(f196,plain,(
% 1.36/0.59    spl9_18 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.36/0.59  fof(f223,plain,(
% 1.36/0.59    ~r1_tarski(sK0,sK2) | spl9_22),
% 1.36/0.59    inference(avatar_component_clause,[],[f222])).
% 1.36/0.59  fof(f480,plain,(
% 1.36/0.59    spl9_29 | spl9_30),
% 1.36/0.59    inference(avatar_split_clause,[],[f479,f358,f355])).
% 1.36/0.59  fof(f479,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.36/0.59    inference(resolution,[],[f93,f71])).
% 1.36/0.59  fof(f71,plain,(
% 1.36/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f42])).
% 1.36/0.59  fof(f42,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.36/0.59    inference(flattening,[],[f41])).
% 1.36/0.59  fof(f41,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.36/0.59    inference(nnf_transformation,[],[f8])).
% 1.36/0.59  fof(f8,axiom,(
% 1.36/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.36/0.59  fof(f93,plain,(
% 1.36/0.59    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X11,sK3)) )),
% 1.36/0.59    inference(superposition,[],[f70,f43])).
% 1.36/0.59  fof(f70,plain,(
% 1.36/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f42])).
% 1.36/0.59  fof(f477,plain,(
% 1.36/0.59    spl9_17 | spl9_18),
% 1.36/0.59    inference(avatar_split_clause,[],[f476,f196,f193])).
% 1.36/0.59  fof(f193,plain,(
% 1.36/0.59    spl9_17 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.36/0.59  fof(f476,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.36/0.59    inference(resolution,[],[f92,f71])).
% 1.36/0.59  fof(f92,plain,(
% 1.36/0.59    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X8,sK2)) )),
% 1.36/0.59    inference(superposition,[],[f69,f43])).
% 1.36/0.59  fof(f69,plain,(
% 1.36/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f42])).
% 1.36/0.59  fof(f459,plain,(
% 1.36/0.59    ~spl9_19 | spl9_11 | ~spl9_21),
% 1.36/0.59    inference(avatar_split_clause,[],[f458,f219,f151,f208])).
% 1.36/0.59  fof(f208,plain,(
% 1.36/0.59    spl9_19 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.36/0.59  fof(f151,plain,(
% 1.36/0.59    spl9_11 <=> k1_xboole_0 = sK1),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.36/0.59  fof(f219,plain,(
% 1.36/0.59    spl9_21 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.36/0.59  fof(f458,plain,(
% 1.36/0.59    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_xboole_0) | ~spl9_21),
% 1.36/0.59    inference(resolution,[],[f220,f52])).
% 1.36/0.59  fof(f52,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f28])).
% 1.36/0.59  fof(f28,plain,(
% 1.36/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.59    inference(flattening,[],[f27])).
% 1.36/0.59  fof(f27,plain,(
% 1.36/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.59    inference(nnf_transformation,[],[f6])).
% 1.36/0.59  fof(f6,axiom,(
% 1.36/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.59  fof(f220,plain,(
% 1.36/0.59    r1_tarski(k1_xboole_0,sK1) | ~spl9_21),
% 1.36/0.59    inference(avatar_component_clause,[],[f219])).
% 1.36/0.59  fof(f435,plain,(
% 1.36/0.59    ~spl9_11),
% 1.36/0.59    inference(avatar_contradiction_clause,[],[f422])).
% 1.36/0.59  fof(f422,plain,(
% 1.36/0.59    $false | ~spl9_11),
% 1.36/0.59    inference(subsumption_resolution,[],[f45,f152])).
% 1.36/0.59  fof(f152,plain,(
% 1.36/0.59    k1_xboole_0 = sK1 | ~spl9_11),
% 1.36/0.59    inference(avatar_component_clause,[],[f151])).
% 1.36/0.59  fof(f416,plain,(
% 1.36/0.59    ~spl9_28 | spl9_2 | ~spl9_27),
% 1.36/0.59    inference(avatar_split_clause,[],[f402,f320,f81,f329])).
% 1.36/0.59  fof(f81,plain,(
% 1.36/0.59    spl9_2 <=> sK1 = sK3),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.36/0.59  fof(f402,plain,(
% 1.36/0.59    sK1 = sK3 | ~r1_tarski(sK1,sK3) | ~spl9_27),
% 1.36/0.59    inference(resolution,[],[f371,f52])).
% 1.36/0.59  fof(f371,plain,(
% 1.36/0.59    r1_tarski(sK3,sK1) | ~spl9_27),
% 1.36/0.59    inference(avatar_component_clause,[],[f320])).
% 1.36/0.59  fof(f410,plain,(
% 1.36/0.59    ~spl9_20 | spl9_1 | ~spl9_22),
% 1.36/0.59    inference(avatar_split_clause,[],[f377,f222,f78,f211])).
% 1.36/0.59  fof(f78,plain,(
% 1.36/0.59    spl9_1 <=> sK0 = sK2),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.36/0.59  fof(f377,plain,(
% 1.36/0.59    sK0 = sK2 | ~r1_tarski(sK2,sK0) | ~spl9_22),
% 1.36/0.59    inference(resolution,[],[f230,f52])).
% 1.36/0.59  fof(f230,plain,(
% 1.36/0.59    r1_tarski(sK0,sK2) | ~spl9_22),
% 1.36/0.59    inference(avatar_component_clause,[],[f222])).
% 1.36/0.59  fof(f353,plain,(
% 1.36/0.59    ~spl9_17 | spl9_19),
% 1.36/0.59    inference(avatar_contradiction_clause,[],[f351])).
% 1.36/0.59  fof(f351,plain,(
% 1.36/0.59    $false | (~spl9_17 | spl9_19)),
% 1.36/0.59    inference(resolution,[],[f253,f194])).
% 1.36/0.59  fof(f194,plain,(
% 1.36/0.59    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_17),
% 1.36/0.59    inference(avatar_component_clause,[],[f193])).
% 1.36/0.59  fof(f253,plain,(
% 1.36/0.59    r2_hidden(sK4(sK1,k1_xboole_0),sK1) | spl9_19),
% 1.36/0.59    inference(resolution,[],[f238,f55])).
% 1.36/0.59  fof(f238,plain,(
% 1.36/0.59    ~r1_tarski(sK1,k1_xboole_0) | spl9_19),
% 1.36/0.59    inference(avatar_component_clause,[],[f208])).
% 1.36/0.59  fof(f263,plain,(
% 1.36/0.59    spl9_21),
% 1.36/0.59    inference(avatar_contradiction_clause,[],[f262])).
% 1.36/0.59  fof(f262,plain,(
% 1.36/0.59    $false | spl9_21),
% 1.36/0.59    inference(subsumption_resolution,[],[f47,f260])).
% 1.36/0.59  fof(f260,plain,(
% 1.36/0.59    ~v1_xboole_0(k1_xboole_0) | spl9_21),
% 1.36/0.59    inference(resolution,[],[f242,f49])).
% 1.36/0.59  fof(f242,plain,(
% 1.36/0.59    r2_hidden(sK4(k1_xboole_0,sK1),k1_xboole_0) | spl9_21),
% 1.36/0.59    inference(resolution,[],[f231,f55])).
% 1.36/0.59  fof(f231,plain,(
% 1.36/0.59    ~r1_tarski(k1_xboole_0,sK1) | spl9_21),
% 1.36/0.59    inference(avatar_component_clause,[],[f219])).
% 1.36/0.59  fof(f83,plain,(
% 1.36/0.59    ~spl9_1 | ~spl9_2),
% 1.36/0.59    inference(avatar_split_clause,[],[f46,f81,f78])).
% 1.36/0.59  fof(f46,plain,(
% 1.36/0.59    sK1 != sK3 | sK0 != sK2),
% 1.36/0.59    inference(cnf_transformation,[],[f26])).
% 1.36/0.59  % SZS output end Proof for theBenchmark
% 1.36/0.59  % (21280)------------------------------
% 1.36/0.59  % (21280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.59  % (21280)Termination reason: Refutation
% 1.36/0.59  
% 1.36/0.59  % (21280)Memory used [KB]: 11129
% 1.36/0.59  % (21280)Time elapsed: 0.173 s
% 1.36/0.59  % (21280)------------------------------
% 1.36/0.59  % (21280)------------------------------
% 1.36/0.59  % (21277)Success in time 0.228 s
%------------------------------------------------------------------------------
