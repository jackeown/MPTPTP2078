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
% DateTime   : Thu Dec  3 12:45:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 142 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 404 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f143,f153,f162,f404,f408,f412])).

fof(f412,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f148,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f148,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f408,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f398,f154])).

fof(f154,plain,
    ( ~ r1_tarski(k9_subset_1(sK0,sK1,sK2),sK0)
    | spl4_6 ),
    inference(resolution,[],[f152,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

% (11876)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f152,plain,
    ( ~ r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_6
  <=> r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f398,plain,(
    r1_tarski(k9_subset_1(sK0,sK1,sK2),sK0) ),
    inference(superposition,[],[f217,f251])).

fof(f251,plain,(
    ! [X1] : k9_subset_1(sK0,X1,sK2) = k4_xboole_0(X1,k4_xboole_0(X1,sK2)) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f217,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(sK1,X3),sK0) ),
    inference(superposition,[],[f62,f201])).

fof(f201,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f197,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f197,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f194,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f59,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f404,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f370,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1)
    | spl4_7 ),
    inference(resolution,[],[f161,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f161,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_7
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f370,plain,(
    ! [X0] : r1_tarski(k9_subset_1(sK0,X0,sK2),X0) ),
    inference(superposition,[],[f33,f251])).

fof(f162,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_4 ),
    inference(avatar_split_clause,[],[f157,f137,f159,f124])).

fof(f124,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f137,plain,
    ( spl4_4
  <=> r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f157,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_4 ),
    inference(superposition,[],[f139,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f139,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f153,plain,
    ( spl4_5
    | ~ spl4_6
    | spl4_3 ),
    inference(avatar_split_clause,[],[f144,f133,f150,f146])).

fof(f133,plain,
    ( spl4_3
  <=> m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f144,plain,
    ( ~ r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl4_3 ),
    inference(resolution,[],[f135,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,
    ( ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f143,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f126,f29])).

fof(f126,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f140,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f122,f137,f133])).

fof(f122,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f31,f41])).

% (11886)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f31,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (11859)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (11875)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (11867)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (11878)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (11882)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (11872)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (11871)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11888)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (11883)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (11873)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (11871)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (11887)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (11880)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (11879)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (11862)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (11861)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.54  % (11860)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.54  % (11863)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.44/0.54  % (11884)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.54  % (11864)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.54  % (11865)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f413,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f140,f143,f153,f162,f404,f408,f412])).
% 1.44/0.55  fof(f412,plain,(
% 1.44/0.55    ~spl4_5),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f409])).
% 1.44/0.55  fof(f409,plain,(
% 1.44/0.55    $false | ~spl4_5),
% 1.44/0.55    inference(resolution,[],[f148,f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f10])).
% 1.44/0.55  fof(f10,axiom,(
% 1.44/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.44/0.55  fof(f148,plain,(
% 1.44/0.55    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_5),
% 1.44/0.55    inference(avatar_component_clause,[],[f146])).
% 1.44/0.55  fof(f146,plain,(
% 1.44/0.55    spl4_5 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.44/0.55  fof(f408,plain,(
% 1.44/0.55    spl4_6),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f405])).
% 1.44/0.55  fof(f405,plain,(
% 1.44/0.55    $false | spl4_6),
% 1.44/0.55    inference(resolution,[],[f398,f154])).
% 1.44/0.55  fof(f154,plain,(
% 1.44/0.55    ~r1_tarski(k9_subset_1(sK0,sK1,sK2),sK0) | spl4_6),
% 1.44/0.55    inference(resolution,[],[f152,f50])).
% 1.44/0.55  fof(f50,plain,(
% 1.44/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f43])).
% 1.44/0.55  fof(f43,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f28])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.55    inference(rectify,[],[f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.55    inference(nnf_transformation,[],[f7])).
% 1.44/0.55  % (11876)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.44/0.55  fof(f152,plain,(
% 1.44/0.55    ~r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl4_6),
% 1.44/0.55    inference(avatar_component_clause,[],[f150])).
% 1.44/0.55  fof(f150,plain,(
% 1.44/0.55    spl4_6 <=> r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.44/0.55  fof(f398,plain,(
% 1.44/0.55    r1_tarski(k9_subset_1(sK0,sK1,sK2),sK0)),
% 1.44/0.55    inference(superposition,[],[f217,f251])).
% 1.44/0.55  fof(f251,plain,(
% 1.44/0.55    ( ! [X1] : (k9_subset_1(sK0,X1,sK2) = k4_xboole_0(X1,k4_xboole_0(X1,sK2))) )),
% 1.44/0.55    inference(resolution,[],[f49,f30])).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.44/0.55    inference(cnf_transformation,[],[f23])).
% 1.44/0.55  fof(f23,plain,(
% 1.44/0.55    (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22,f21])).
% 1.44/0.55  fof(f21,plain,(
% 1.44/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f14,plain,(
% 1.44/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,negated_conjecture,(
% 1.44/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.44/0.55    inference(negated_conjecture,[],[f12])).
% 1.44/0.55  fof(f12,conjecture,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f48,f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f20])).
% 1.44/0.55  fof(f20,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f11])).
% 1.44/0.55  fof(f11,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.44/0.55  fof(f217,plain,(
% 1.44/0.55    ( ! [X3] : (r1_tarski(k4_xboole_0(sK1,X3),sK0)) )),
% 1.44/0.55    inference(superposition,[],[f62,f201])).
% 1.44/0.55  fof(f201,plain,(
% 1.44/0.55    sK0 = k2_xboole_0(sK1,sK0)),
% 1.44/0.55    inference(resolution,[],[f197,f40])).
% 1.44/0.55  fof(f40,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f16])).
% 1.44/0.55  fof(f16,plain,(
% 1.44/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.44/0.55  fof(f197,plain,(
% 1.44/0.55    r1_tarski(sK1,sK0)),
% 1.44/0.55    inference(resolution,[],[f194,f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.55    inference(cnf_transformation,[],[f23])).
% 1.44/0.55  fof(f194,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(resolution,[],[f53,f32])).
% 1.44/0.55  fof(f53,plain,(
% 1.44/0.55    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(resolution,[],[f36,f51])).
% 1.44/0.55  fof(f51,plain,(
% 1.44/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f42])).
% 1.44/0.55  fof(f42,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f28])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.44/0.55    inference(nnf_transformation,[],[f15])).
% 1.44/0.55  fof(f15,plain,(
% 1.44/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.44/0.55  fof(f62,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X0))) )),
% 1.44/0.55    inference(superposition,[],[f59,f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.44/0.55  fof(f59,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0))) )),
% 1.44/0.55    inference(resolution,[],[f46,f33])).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.44/0.55  fof(f404,plain,(
% 1.44/0.55    spl4_7),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f401])).
% 1.44/0.55  fof(f401,plain,(
% 1.44/0.55    $false | spl4_7),
% 1.44/0.55    inference(resolution,[],[f370,f163])).
% 1.44/0.55  fof(f163,plain,(
% 1.44/0.55    ~r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1) | spl4_7),
% 1.44/0.55    inference(resolution,[],[f161,f47])).
% 1.44/0.55  fof(f47,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f19])).
% 1.44/0.55  fof(f19,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.44/0.55  fof(f161,plain,(
% 1.44/0.55    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | spl4_7),
% 1.44/0.55    inference(avatar_component_clause,[],[f159])).
% 1.44/0.55  fof(f159,plain,(
% 1.44/0.55    spl4_7 <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.44/0.55  fof(f370,plain,(
% 1.44/0.55    ( ! [X0] : (r1_tarski(k9_subset_1(sK0,X0,sK2),X0)) )),
% 1.44/0.55    inference(superposition,[],[f33,f251])).
% 1.44/0.55  fof(f162,plain,(
% 1.44/0.55    ~spl4_1 | ~spl4_7 | spl4_4),
% 1.44/0.55    inference(avatar_split_clause,[],[f157,f137,f159,f124])).
% 1.44/0.55  fof(f124,plain,(
% 1.44/0.55    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.44/0.55  fof(f137,plain,(
% 1.44/0.55    spl4_4 <=> r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.44/0.55  fof(f157,plain,(
% 1.44/0.55    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_4),
% 1.44/0.55    inference(superposition,[],[f139,f41])).
% 1.44/0.55  fof(f41,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f17])).
% 1.44/0.55  fof(f17,plain,(
% 1.44/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.44/0.55  fof(f139,plain,(
% 1.44/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | spl4_4),
% 1.44/0.55    inference(avatar_component_clause,[],[f137])).
% 1.44/0.55  fof(f153,plain,(
% 1.44/0.55    spl4_5 | ~spl4_6 | spl4_3),
% 1.44/0.55    inference(avatar_split_clause,[],[f144,f133,f150,f146])).
% 1.44/0.55  fof(f133,plain,(
% 1.44/0.55    spl4_3 <=> m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.44/0.55  fof(f144,plain,(
% 1.44/0.55    ~r2_hidden(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl4_3),
% 1.44/0.55    inference(resolution,[],[f135,f37])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f135,plain,(
% 1.44/0.55    ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl4_3),
% 1.44/0.55    inference(avatar_component_clause,[],[f133])).
% 1.44/0.55  fof(f143,plain,(
% 1.44/0.55    spl4_1),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f141])).
% 1.44/0.55  fof(f141,plain,(
% 1.44/0.55    $false | spl4_1),
% 1.44/0.55    inference(resolution,[],[f126,f29])).
% 1.44/0.55  fof(f126,plain,(
% 1.44/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 1.44/0.55    inference(avatar_component_clause,[],[f124])).
% 1.44/0.55  fof(f140,plain,(
% 1.44/0.55    ~spl4_3 | ~spl4_4),
% 1.44/0.55    inference(avatar_split_clause,[],[f122,f137,f133])).
% 1.44/0.55  fof(f122,plain,(
% 1.44/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,k9_subset_1(sK0,sK1,sK2))) | ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.44/0.55    inference(superposition,[],[f31,f41])).
% 1.44/0.55  % (11886)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  fof(f31,plain,(
% 1.44/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.44/0.55    inference(cnf_transformation,[],[f23])).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (11871)------------------------------
% 1.44/0.55  % (11871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (11871)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (11871)Memory used [KB]: 6524
% 1.44/0.55  % (11871)Time elapsed: 0.130 s
% 1.44/0.55  % (11871)------------------------------
% 1.44/0.55  % (11871)------------------------------
% 1.44/0.55  % (11881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  % (11869)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.55  % (11858)Success in time 0.192 s
%------------------------------------------------------------------------------
