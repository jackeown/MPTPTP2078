%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 168 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 ( 395 expanded)
%              Number of equality atoms :   49 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f92,f162,f168,f517,f539,f585])).

fof(f585,plain,
    ( spl5_2
    | ~ spl5_12
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f577,f537,f166,f81])).

fof(f81,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f166,plain,
    ( spl5_12
  <=> sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f537,plain,
    ( spl5_58
  <=> r1_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f577,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_12
    | ~ spl5_58 ),
    inference(superposition,[],[f151,f559])).

fof(f559,plain,
    ( ! [X0] : sK1 = k3_xboole_0(sK1,X0)
    | ~ spl5_12
    | ~ spl5_58 ),
    inference(resolution,[],[f549,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f549,plain,
    ( ! [X1] : r1_tarski(sK1,X1)
    | ~ spl5_12
    | ~ spl5_58 ),
    inference(resolution,[],[f547,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f547,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_12
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f546,f167])).

fof(f167,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f546,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f541,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f541,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k3_subset_1(sK0,sK1),sK1))
    | ~ spl5_58 ),
    inference(resolution,[],[f538,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f538,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f537])).

fof(f151,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(superposition,[],[f150,f50])).

fof(f150,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X4,X4),X4) ),
    inference(resolution,[],[f63,f98])).

fof(f98,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f72,f48])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f539,plain,
    ( spl5_58
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f535,f515,f537])).

fof(f515,plain,
    ( spl5_54
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f535,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl5_54 ),
    inference(superposition,[],[f72,f516])).

fof(f516,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f515])).

fof(f517,plain,
    ( spl5_54
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f511,f90,f515])).

fof(f90,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f511,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f73,f91])).

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f168,plain,
    ( spl5_12
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f164,f85,f166])).

fof(f85,plain,
    ( spl5_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f164,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f86,f58])).

fof(f86,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f162,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f79,f157])).

fof(f157,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f131,f151])).

fof(f131,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,k5_xboole_0(X2,X2)),X3) ),
    inference(resolution,[],[f61,f127])).

fof(f127,plain,(
    ! [X6,X7] : ~ r2_hidden(X6,k3_xboole_0(X7,k5_xboole_0(X7,X7))) ),
    inference(forward_demodulation,[],[f124,f50])).

fof(f124,plain,(
    ! [X6,X7] : ~ r2_hidden(X6,k3_xboole_0(k5_xboole_0(X7,X7),X7)) ),
    inference(resolution,[],[f57,f98])).

fof(f79,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
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

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f88,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f71,f81,f85])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f44,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f76,f81,f78])).

fof(f76,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f70])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (20802)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.47  % (20802)Refutation not found, incomplete strategy% (20802)------------------------------
% 0.22/0.47  % (20802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20819)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.48  % (20810)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.48  % (20802)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (20802)Memory used [KB]: 10746
% 0.22/0.48  % (20802)Time elapsed: 0.076 s
% 0.22/0.48  % (20802)------------------------------
% 0.22/0.48  % (20802)------------------------------
% 0.22/0.50  % (20810)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f586,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f83,f88,f92,f162,f168,f517,f539,f585])).
% 0.22/0.50  fof(f585,plain,(
% 0.22/0.50    spl5_2 | ~spl5_12 | ~spl5_58),
% 0.22/0.50    inference(avatar_split_clause,[],[f577,f537,f166,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl5_2 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    spl5_12 <=> sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.50  fof(f537,plain,(
% 0.22/0.50    spl5_58 <=> r1_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.22/0.50  fof(f577,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | (~spl5_12 | ~spl5_58)),
% 0.22/0.50    inference(superposition,[],[f151,f559])).
% 0.22/0.50  fof(f559,plain,(
% 0.22/0.50    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0)) ) | (~spl5_12 | ~spl5_58)),
% 0.22/0.50    inference(resolution,[],[f549,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f549,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(sK1,X1)) ) | (~spl5_12 | ~spl5_58)),
% 0.22/0.50    inference(resolution,[],[f547,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.50  fof(f547,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl5_12 | ~spl5_58)),
% 0.22/0.50    inference(forward_demodulation,[],[f546,f167])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl5_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f166])).
% 0.22/0.50  fof(f546,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))) ) | ~spl5_58),
% 0.22/0.50    inference(forward_demodulation,[],[f541,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f541,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k3_subset_1(sK0,sK1),sK1))) ) | ~spl5_58),
% 0.22/0.50    inference(resolution,[],[f538,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f538,plain,(
% 0.22/0.50    r1_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl5_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f537])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X1,X1))) )),
% 0.22/0.50    inference(superposition,[],[f150,f50])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X4,X4),X4)) )),
% 0.22/0.50    inference(resolution,[],[f63,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 0.22/0.50    inference(superposition,[],[f72,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    inference(rectify,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f49,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.50  fof(f539,plain,(
% 0.22/0.50    spl5_58 | ~spl5_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f535,f515,f537])).
% 0.22/0.50  fof(f515,plain,(
% 0.22/0.50    spl5_54 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.22/0.50  fof(f535,plain,(
% 0.22/0.50    r1_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl5_54),
% 0.22/0.50    inference(superposition,[],[f72,f516])).
% 0.22/0.50  fof(f516,plain,(
% 0.22/0.50    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f515])).
% 0.22/0.50  fof(f517,plain,(
% 0.22/0.50    spl5_54 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f511,f90,f515])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f511,plain,(
% 0.22/0.50    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f73,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f59,f51])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl5_12 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f164,f85,f166])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl5_3 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f86,f58])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl5_1),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f161])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    $false | spl5_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f79,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 0.22/0.50    inference(superposition,[],[f131,f151])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,k5_xboole_0(X2,X2)),X3)) )),
% 0.22/0.50    inference(resolution,[],[f61,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X6,X7] : (~r2_hidden(X6,k3_xboole_0(X7,k5_xboole_0(X7,X7)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f124,f50])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X6,X7] : (~r2_hidden(X6,k3_xboole_0(k5_xboole_0(X7,X7),X7))) )),
% 0.22/0.50    inference(resolution,[],[f57,f98])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl5_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f90])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl5_3 | spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f71,f81,f85])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f44,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~spl5_1 | ~spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f76,f81,f78])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.51    inference(inner_rewriting,[],[f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f45,f47])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (20810)------------------------------
% 0.22/0.51  % (20810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20810)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (20810)Memory used [KB]: 11129
% 0.22/0.51  % (20810)Time elapsed: 0.115 s
% 0.22/0.51  % (20810)------------------------------
% 0.22/0.51  % (20810)------------------------------
% 0.22/0.51  % (20790)Success in time 0.148 s
%------------------------------------------------------------------------------
