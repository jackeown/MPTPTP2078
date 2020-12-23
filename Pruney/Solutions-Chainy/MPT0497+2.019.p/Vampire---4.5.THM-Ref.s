%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 164 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  268 ( 450 expanded)
%              Number of equality atoms :   78 ( 153 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f90,f94,f102,f142,f153,f156,f167,f211])).

fof(f211,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl7_8 ),
    inference(resolution,[],[f166,f103])).

fof(f103,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f52,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f166,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl7_8
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f167,plain,
    ( spl7_8
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f163,f100,f92,f85,f82,f165])).

fof(f82,plain,
    ( spl7_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f85,plain,
    ( spl7_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f92,plain,
    ( spl7_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f100,plain,
    ( spl7_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f163,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f162,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f162,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0))
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f161,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f161,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f157,f110])).

fof(f110,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))
    | ~ spl7_3 ),
    inference(resolution,[],[f76,f93])).

fof(f93,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f157,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0)))
    | spl7_2 ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).

% (26356)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f31,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f86,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f156,plain,
    ( ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f154,f151,f92])).

fof(f151,plain,
    ( spl7_7
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f154,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_7 ),
    inference(resolution,[],[f152,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( ~ spl7_7
    | spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f149,f140,f82,f151])).

fof(f140,plain,
    ( spl7_6
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f149,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_6 ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_6 ),
    inference(superposition,[],[f50,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f142,plain,
    ( spl7_6
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f138,f100,f92,f85,f140])).

fof(f138,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f132,f101])).

fof(f132,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f123,f103])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(X0,k1_relat_1(k7_relat_1(sK1,sK0))),sK5(X0,k1_relat_1(k7_relat_1(sK1,sK0)))),X0)
        | k1_relat_1(X0) = k1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f120,f89])).

fof(f89,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f120,plain,
    ( ! [X19,X20] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X20)
        | k1_relat_1(k7_relat_1(sK1,X20)) = k1_relat_1(X19)
        | r2_hidden(k4_tarski(sK4(X19,k1_relat_1(k7_relat_1(sK1,X20))),sK5(X19,k1_relat_1(k7_relat_1(sK1,X20)))),X19) )
    | ~ spl7_3 ),
    inference(resolution,[],[f65,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0)))
        | ~ r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f74,f110])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f102,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f94,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f90,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f46,f85,f82])).

fof(f46,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f47,f85,f82])).

fof(f47,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26359)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (26378)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (26386)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (26362)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (26378)Refutation not found, incomplete strategy% (26378)------------------------------
% 0.21/0.49  % (26378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26378)Memory used [KB]: 10746
% 0.21/0.49  % (26378)Time elapsed: 0.005 s
% 0.21/0.49  % (26378)------------------------------
% 0.21/0.49  % (26378)------------------------------
% 0.21/0.49  % (26377)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (26369)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (26360)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (26375)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (26375)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f87,f90,f94,f102,f142,f153,f156,f167,f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~spl7_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    $false | ~spl7_8),
% 0.21/0.51    inference(resolution,[],[f166,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f52,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(flattening,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(nnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) | ~spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl7_8 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl7_8 | ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f100,f92,f85,f82,f165])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl7_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl7_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl7_3 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl7_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f162,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0)) | (~spl7_1 | spl7_2 | ~spl7_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f161,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | (spl7_2 | ~spl7_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f157,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) ) | ~spl7_3),
% 0.21/0.51    inference(resolution,[],[f76,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f61,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f53,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))) | spl7_2),
% 0.21/0.51    inference(resolution,[],[f86,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f55,f73])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).
% 0.21/0.51  % (26356)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~spl7_3 | spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f154,f151,f92])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl7_7 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | spl7_7),
% 0.21/0.51    inference(resolution,[],[f152,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~spl7_7 | spl7_1 | ~spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f140,f82,f151])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl7_6 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl7_6),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl7_6),
% 0.21/0.51    inference(superposition,[],[f50,f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f140])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl7_6 | ~spl7_2 | ~spl7_3 | ~spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f138,f100,f92,f85,f140])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f132,f101])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    k1_relat_1(k1_xboole_0) = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl7_2 | ~spl7_3)),
% 0.21/0.51    inference(resolution,[],[f123,f103])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k4_tarski(sK4(X0,k1_relat_1(k7_relat_1(sK1,sK0))),sK5(X0,k1_relat_1(k7_relat_1(sK1,sK0)))),X0) | k1_relat_1(X0) = k1_relat_1(k7_relat_1(sK1,sK0))) ) | (~spl7_2 | ~spl7_3)),
% 0.21/0.51    inference(resolution,[],[f120,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X19,X20] : (~r1_xboole_0(k1_relat_1(sK1),X20) | k1_relat_1(k7_relat_1(sK1,X20)) = k1_relat_1(X19) | r2_hidden(k4_tarski(sK4(X19,k1_relat_1(k7_relat_1(sK1,X20))),sK5(X19,k1_relat_1(k7_relat_1(sK1,X20)))),X19)) ) | ~spl7_3),
% 0.21/0.51    inference(resolution,[],[f65,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0))) | ~r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl7_3),
% 0.21/0.51    inference(superposition,[],[f74,f110])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f56,f73])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.51    inference(rectify,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f100])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f92])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl7_1 | spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f85,f82])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~spl7_1 | ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f85,f82])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26375)------------------------------
% 0.21/0.51  % (26375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26375)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26375)Memory used [KB]: 10874
% 0.21/0.51  % (26375)Time elapsed: 0.098 s
% 0.21/0.51  % (26375)------------------------------
% 0.21/0.51  % (26375)------------------------------
% 0.21/0.51  % (26352)Success in time 0.153 s
%------------------------------------------------------------------------------
