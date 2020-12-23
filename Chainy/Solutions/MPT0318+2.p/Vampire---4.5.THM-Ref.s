%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0318+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 140 expanded)
%              Number of equality atoms :   62 ( 108 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f757,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f592,f596,f741,f756])).

fof(f756,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f754,f595])).

fof(f595,plain,
    ( k1_xboole_0 != sK0
    | spl5_3 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f754,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f752,f598])).

fof(f598,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f556,f559])).

fof(f559,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f556,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f380])).

fof(f380,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f752,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f751])).

fof(f751,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(superposition,[],[f495,f588])).

fof(f588,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f495,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f453])).

fof(f453,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f452])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f323])).

fof(f323,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f741,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f740])).

fof(f740,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f739,f598])).

fof(f739,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f737,f595])).

fof(f737,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f734])).

fof(f734,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f495,f591])).

fof(f591,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl5_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f596,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f476,f594])).

fof(f476,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f451])).

fof(f451,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f423,f450])).

% (16229)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
fof(f450,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f423,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f342])).

fof(f342,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f341])).

fof(f341,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f592,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f477,f590,f587])).

fof(f477,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f451])).
%------------------------------------------------------------------------------
