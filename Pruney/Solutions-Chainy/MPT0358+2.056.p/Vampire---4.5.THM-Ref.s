%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 178 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  278 ( 577 expanded)
%              Number of equality atoms :   56 ( 129 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f75,f96,f103,f119,f124,f137,f147,f159])).

fof(f159,plain,
    ( spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f155,f145,f64])).

fof(f64,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f145,plain,
    ( spl5_10
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f155,plain,
    ( k1_xboole_0 = sK1
    | spl5_10 ),
    inference(resolution,[],[f146,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f146,plain,
    ( ~ r2_hidden(sK2(sK1),sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( ~ spl5_10
    | ~ spl5_3
    | spl5_9 ),
    inference(avatar_split_clause,[],[f141,f135,f68,f145])).

fof(f68,plain,
    ( spl5_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

% (24036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f135,plain,
    ( spl5_9
  <=> r2_hidden(sK2(sK1),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f141,plain,
    ( ~ r2_hidden(sK2(sK1),sK1)
    | ~ spl5_3
    | spl5_9 ),
    inference(resolution,[],[f140,f69])).

fof(f69,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f140,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(sK2(sK1),X2) )
    | spl5_9 ),
    inference(resolution,[],[f136,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f136,plain,
    ( ~ r2_hidden(sK2(sK1),k3_subset_1(sK0,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f133,f122,f135,f64])).

fof(f122,plain,
    ( spl5_8
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f133,plain,
    ( ~ r2_hidden(sK2(sK1),k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1
    | ~ spl5_8 ),
    inference(superposition,[],[f84,f123])).

fof(f123,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0),k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f124,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f89,f73,f122])).

fof(f73,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f49,f74])).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f119,plain,
    ( spl5_7
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f115,f94,f61,f101])).

fof(f101,plain,
    ( spl5_7
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f61,plain,
    ( spl5_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f94,plain,
    ( spl5_6
  <=> sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f115,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | spl5_1
    | ~ spl5_6 ),
    inference(resolution,[],[f114,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k1_xboole_0,sK0),X0)
    | spl5_1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f111,f95])).

fof(f95,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f111,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)),X0)
    | spl5_1 ),
    inference(resolution,[],[f110,f62])).

fof(f62,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_xboole_0,X1)
      | ~ r2_hidden(sK3(k1_xboole_0,X1),X0) ) ),
    inference(superposition,[],[f85,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK3(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X2)))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f57,f38])).

fof(f103,plain,
    ( ~ spl5_7
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f99,f94,f61,f101])).

fof(f99,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl5_1
    | ~ spl5_6 ),
    inference(superposition,[],[f62,f95])).

fof(f96,plain,
    ( spl5_6
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f92,f73,f64,f94])).

fof(f92,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f91,f48])).

% (24043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f91,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f89,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f75,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f29,f73])).

% (24055)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f71,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f47,f64,f68])).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f30,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f59,f64,f61])).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.51  % (24052)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (24044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (24052)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f66,f71,f75,f96,f103,f119,f124,f137,f147,f159])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl5_2 | spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f155,f145,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl5_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl5_10 <=> r2_hidden(sK2(sK1),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | spl5_10),
% 0.22/0.53    inference(resolution,[],[f146,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK1),sK1) | spl5_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f145])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~spl5_10 | ~spl5_3 | spl5_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f141,f135,f68,f145])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl5_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  % (24036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl5_9 <=> r2_hidden(sK2(sK1),k3_subset_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK1),sK1) | (~spl5_3 | spl5_9)),
% 0.22/0.53    inference(resolution,[],[f140,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl5_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f68])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) | ~r2_hidden(sK2(sK1),X2)) ) | spl5_9),
% 0.22/0.53    inference(resolution,[],[f136,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK1),k3_subset_1(sK0,sK1)) | spl5_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl5_2 | ~spl5_9 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f133,f122,f135,f64])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    spl5_8 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK1),k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1 | ~spl5_8),
% 0.22/0.53    inference(superposition,[],[f84,f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f122])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0),k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(resolution,[],[f57,f34])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.22/0.53    inference(equality_resolution,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.22/0.53    inference(definition_unfolding,[],[f41,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl5_8 | ~spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f89,f73,f122])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_4),
% 0.22/0.53    inference(resolution,[],[f49,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f73])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f36,f35])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl5_7 | spl5_1 | ~spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f115,f94,f61,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl5_7 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl5_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl5_6 <=> sK0 = k3_subset_1(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    r1_tarski(k1_xboole_0,sK0) | (spl5_1 | ~spl5_6)),
% 0.22/0.53    inference(resolution,[],[f114,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK3(k1_xboole_0,sK0),X0)) ) | (spl5_1 | ~spl5_6)),
% 0.22/0.53    inference(forward_demodulation,[],[f111,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    sK0 = k3_subset_1(sK0,k1_xboole_0) | ~spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f94])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK3(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)),X0)) ) | spl5_1),
% 0.22/0.53    inference(resolution,[],[f110,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,X1) | ~r2_hidden(sK3(k1_xboole_0,X1),X0)) )),
% 0.22/0.53    inference(superposition,[],[f85,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f33,f35])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (~r2_hidden(sK3(X2,X3),k5_xboole_0(X4,k3_xboole_0(X4,X2))) | r1_tarski(X2,X3)) )),
% 0.22/0.53    inference(resolution,[],[f57,f38])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ~spl5_7 | spl5_1 | ~spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f99,f94,f61,f101])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK0) | (spl5_1 | ~spl5_6)),
% 0.22/0.53    inference(superposition,[],[f62,f95])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl5_6 | ~spl5_2 | ~spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f92,f73,f64,f94])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    sK0 = k3_subset_1(sK0,k1_xboole_0) | (~spl5_2 | ~spl5_4)),
% 0.22/0.53    inference(forward_demodulation,[],[f91,f48])).
% 0.22/0.54  % (24043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    k3_subset_1(sK0,k1_xboole_0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) | (~spl5_2 | ~spl5_4)),
% 0.22/0.54    inference(forward_demodulation,[],[f89,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f64])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f29,f73])).
% 0.22/0.54  % (24055)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f8])).
% 0.22/0.54  fof(f8,conjecture,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl5_3 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f64,f68])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f59,f64,f61])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.54    inference(inner_rewriting,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f32])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24052)------------------------------
% 0.22/0.54  % (24052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24052)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24052)Memory used [KB]: 10746
% 0.22/0.54  % (24052)Time elapsed: 0.096 s
% 0.22/0.54  % (24052)------------------------------
% 0.22/0.54  % (24052)------------------------------
% 0.22/0.54  % (24043)Refutation not found, incomplete strategy% (24043)------------------------------
% 0.22/0.54  % (24043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24043)Memory used [KB]: 10618
% 0.22/0.54  % (24043)Time elapsed: 0.128 s
% 0.22/0.54  % (24043)------------------------------
% 0.22/0.54  % (24043)------------------------------
% 0.22/0.55  % (24032)Success in time 0.17 s
%------------------------------------------------------------------------------
