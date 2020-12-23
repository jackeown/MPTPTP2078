%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 158 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  202 ( 491 expanded)
%              Number of equality atoms :   63 ( 193 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f802,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f118,f332,f341,f798])).

fof(f798,plain,
    ( ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f796,f51])).

fof(f51,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f796,plain,
    ( sK0 = sK1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f748,f795])).

fof(f795,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f788,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f788,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f376,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f376,plain,
    ( ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl6_2 ),
    inference(superposition,[],[f74,f351])).

fof(f351,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f349,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f349,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f344,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f344,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK5(X3,sK1),sK0)
        | r1_tarski(X3,sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f101,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f74,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f748,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f741,f53])).

fof(f741,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl6_4 ),
    inference(superposition,[],[f201,f52])).

fof(f201,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X0))
    | ~ spl6_4 ),
    inference(superposition,[],[f74,f166])).

fof(f166,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f165,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f165,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))
    | ~ spl6_4 ),
    inference(resolution,[],[f163,f90])).

fof(f163,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f127,f70])).

fof(f127,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK1,X1),sK0)
        | r1_tarski(sK1,X1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f113,f69])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_4
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f341,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f333,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f333,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_1 ),
    inference(resolution,[],[f98,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f98,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_1
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f332,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f123,f100,f97])).

fof(f123,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f94,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f94,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f78,f48])).

fof(f48,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f115,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(resolution,[],[f110,f54])).

fof(f110,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_3
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f114,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f107,f112,f109])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f93,f78])).

fof(f93,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f77,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.34  % CPULimit   : 60
% 0.18/0.34  % WCLimit    : 600
% 0.18/0.34  % DateTime   : Tue Dec  1 18:10:12 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.20/0.50  % (4218)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (4211)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (4224)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (4222)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (4210)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (4230)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (4235)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (4214)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (4232)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (4219)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (4228)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (4207)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (4206)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (4206)Refutation not found, incomplete strategy% (4206)------------------------------
% 0.20/0.53  % (4206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4206)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4206)Memory used [KB]: 1663
% 0.20/0.53  % (4206)Time elapsed: 0.125 s
% 0.20/0.53  % (4206)------------------------------
% 0.20/0.53  % (4206)------------------------------
% 0.20/0.53  % (4208)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (4223)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (4209)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (4212)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (4231)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (4220)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (4213)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (4233)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (4234)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (4221)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (4217)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (4225)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (4217)Refutation not found, incomplete strategy% (4217)------------------------------
% 0.20/0.54  % (4217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4217)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4217)Memory used [KB]: 10618
% 0.20/0.54  % (4217)Time elapsed: 0.139 s
% 0.20/0.54  % (4217)------------------------------
% 0.20/0.54  % (4217)------------------------------
% 0.20/0.54  % (4216)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (4216)Refutation not found, incomplete strategy% (4216)------------------------------
% 0.20/0.54  % (4216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4216)Memory used [KB]: 10618
% 0.20/0.54  % (4216)Time elapsed: 0.138 s
% 0.20/0.54  % (4216)------------------------------
% 0.20/0.54  % (4216)------------------------------
% 0.20/0.55  % (4223)Refutation not found, incomplete strategy% (4223)------------------------------
% 0.20/0.55  % (4223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4223)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4223)Memory used [KB]: 10618
% 0.20/0.55  % (4223)Time elapsed: 0.150 s
% 0.20/0.55  % (4223)------------------------------
% 0.20/0.55  % (4223)------------------------------
% 0.20/0.55  % (4227)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (4226)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (4227)Refutation not found, incomplete strategy% (4227)------------------------------
% 0.20/0.55  % (4227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4227)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4227)Memory used [KB]: 1663
% 0.20/0.55  % (4227)Time elapsed: 0.143 s
% 0.20/0.55  % (4227)------------------------------
% 0.20/0.55  % (4227)------------------------------
% 0.20/0.55  % (4229)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (4226)Refutation not found, incomplete strategy% (4226)------------------------------
% 0.20/0.55  % (4226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4226)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4226)Memory used [KB]: 10746
% 0.20/0.55  % (4226)Time elapsed: 0.150 s
% 0.20/0.55  % (4226)------------------------------
% 0.20/0.55  % (4226)------------------------------
% 0.20/0.55  % (4215)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (4215)Refutation not found, incomplete strategy% (4215)------------------------------
% 0.20/0.55  % (4215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4215)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4215)Memory used [KB]: 10618
% 0.20/0.55  % (4215)Time elapsed: 0.149 s
% 0.20/0.55  % (4215)------------------------------
% 0.20/0.55  % (4215)------------------------------
% 0.20/0.55  % (4214)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f802,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f114,f118,f332,f341,f798])).
% 0.20/0.55  fof(f798,plain,(
% 0.20/0.55    ~spl6_2 | ~spl6_4),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f797])).
% 0.20/0.55  fof(f797,plain,(
% 0.20/0.55    $false | (~spl6_2 | ~spl6_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f796,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    sK0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    inference(negated_conjecture,[],[f23])).
% 0.20/0.55  fof(f23,conjecture,(
% 0.20/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.20/0.55  fof(f796,plain,(
% 0.20/0.55    sK0 = sK1 | (~spl6_2 | ~spl6_4)),
% 0.20/0.55    inference(backward_demodulation,[],[f748,f795])).
% 0.20/0.55  fof(f795,plain,(
% 0.20/0.55    sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl6_2),
% 0.20/0.55    inference(forward_demodulation,[],[f788,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.55  fof(f788,plain,(
% 0.20/0.55    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 0.20/0.55    inference(superposition,[],[f376,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.55  fof(f376,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) ) | ~spl6_2),
% 0.20/0.55    inference(superposition,[],[f74,f351])).
% 0.20/0.55  fof(f351,plain,(
% 0.20/0.55    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl6_2),
% 0.20/0.55    inference(resolution,[],[f349,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f72,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.55  fof(f349,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | ~spl6_2),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f346])).
% 0.20/0.55  fof(f346,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl6_2),
% 0.20/0.55    inference(resolution,[],[f344,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.55  fof(f344,plain,(
% 0.20/0.55    ( ! [X3] : (~r2_hidden(sK5(X3,sK1),sK0) | r1_tarski(X3,sK1)) ) | ~spl6_2),
% 0.20/0.55    inference(resolution,[],[f101,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f100])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    spl6_2 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.55  fof(f748,plain,(
% 0.20/0.55    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl6_4),
% 0.20/0.55    inference(forward_demodulation,[],[f741,f53])).
% 0.20/0.55  fof(f741,plain,(
% 0.20/0.55    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl6_4),
% 0.20/0.55    inference(superposition,[],[f201,f52])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X0))) ) | ~spl6_4),
% 0.20/0.55    inference(superposition,[],[f74,f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl6_4),
% 0.20/0.55    inference(forward_demodulation,[],[f165,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.55  fof(f165,plain,(
% 0.20/0.55    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) | ~spl6_4),
% 0.20/0.55    inference(resolution,[],[f163,f90])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    r1_tarski(sK1,sK0) | ~spl6_4),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f161])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl6_4),
% 0.20/0.55    inference(resolution,[],[f127,f70])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    ( ! [X1] : (r2_hidden(sK5(sK1,X1),sK0) | r1_tarski(sK1,X1)) ) | ~spl6_4),
% 0.20/0.55    inference(resolution,[],[f113,f69])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl6_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f112])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    spl6_4 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    ~spl6_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f340])).
% 0.20/0.55  fof(f340,plain,(
% 0.20/0.55    $false | ~spl6_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f333,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f333,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl6_1),
% 0.20/0.55    inference(resolution,[],[f98,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    spl6_1 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.55  fof(f332,plain,(
% 0.20/0.55    spl6_1 | spl6_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f123,f100,f97])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ( ! [X6,X7] : (~r2_hidden(X6,sK0) | ~r2_hidden(X7,sK1) | r2_hidden(X6,sK1)) )),
% 0.20/0.55    inference(resolution,[],[f94,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.55    inference(flattening,[],[f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.55    inference(nnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.55    inference(superposition,[],[f78,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    ~spl6_3),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    $false | ~spl6_3),
% 0.20/0.55    inference(subsumption_resolution,[],[f115,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl6_3),
% 0.20/0.55    inference(resolution,[],[f110,f54])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl6_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl6_3 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl6_3 | spl6_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f107,f112,f109])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f93,f78])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) )),
% 0.20/0.55    inference(superposition,[],[f77,f48])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (4214)------------------------------
% 0.20/0.55  % (4214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4214)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (4214)Memory used [KB]: 11129
% 0.20/0.55  % (4214)Time elapsed: 0.134 s
% 0.20/0.55  % (4214)------------------------------
% 0.20/0.55  % (4214)------------------------------
% 0.20/0.55  % (4205)Success in time 0.197 s
%------------------------------------------------------------------------------
