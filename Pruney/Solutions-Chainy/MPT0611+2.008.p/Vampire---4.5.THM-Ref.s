%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 155 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  241 ( 456 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f369,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f53,f57,f65,f69,f77,f122,f158,f216,f254,f274,f290,f342,f349,f368])).

fof(f368,plain,
    ( spl2_1
    | ~ spl2_6
    | ~ spl2_60 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | spl2_1
    | ~ spl2_6
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f353,f33])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f353,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_6
    | ~ spl2_60 ),
    inference(resolution,[],[f348,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f348,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl2_60
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f349,plain,
    ( spl2_60
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f344,f340,f51,f41,f346])).

fof(f41,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f340,plain,
    ( spl2_59
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK1)))
        | r1_xboole_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f344,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_59 ),
    inference(subsumption_resolution,[],[f343,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f343,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_5
    | ~ spl2_59 ),
    inference(resolution,[],[f341,f52])).

fof(f52,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f341,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK1)))
        | r1_xboole_0(X3,sK0) )
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f340])).

fof(f342,plain,
    ( spl2_59
    | ~ spl2_9
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f336,f288,f67,f340])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f288,plain,
    ( spl2_50
  <=> ! [X6] : k2_zfmisc_1(X6,k2_relat_1(sK1)) = k4_xboole_0(k2_zfmisc_1(X6,k2_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f336,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK1)))
        | r1_xboole_0(X3,sK0) )
    | ~ spl2_9
    | ~ spl2_50 ),
    inference(superposition,[],[f68,f289])).

fof(f289,plain,
    ( ! [X6] : k2_zfmisc_1(X6,k2_relat_1(sK1)) = k4_xboole_0(k2_zfmisc_1(X6,k2_relat_1(sK1)),sK0)
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f288])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f290,plain,
    ( spl2_50
    | ~ spl2_8
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f277,f272,f63,f288])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f272,plain,
    ( spl2_47
  <=> ! [X7] : r1_xboole_0(k2_zfmisc_1(X7,k2_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f277,plain,
    ( ! [X6] : k2_zfmisc_1(X6,k2_relat_1(sK1)) = k4_xboole_0(k2_zfmisc_1(X6,k2_relat_1(sK1)),sK0)
    | ~ spl2_8
    | ~ spl2_47 ),
    inference(resolution,[],[f273,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f273,plain,
    ( ! [X7] : r1_xboole_0(k2_zfmisc_1(X7,k2_relat_1(sK1)),sK0)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( spl2_47
    | ~ spl2_6
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f258,f252,f55,f272])).

fof(f252,plain,
    ( spl2_43
  <=> ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f258,plain,
    ( ! [X7] : r1_xboole_0(k2_zfmisc_1(X7,k2_relat_1(sK1)),sK0)
    | ~ spl2_6
    | ~ spl2_43 ),
    inference(resolution,[],[f253,f56])).

fof(f253,plain,
    ( ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl2_43
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f250,f214,f51,f46,f252])).

fof(f46,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f214,plain,
    ( spl2_36
  <=> ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,k2_zfmisc_1(X3,k2_relat_1(sK0)))
        | r1_xboole_0(X5,k2_zfmisc_1(X4,k2_relat_1(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f250,plain,
    ( ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f249,f48])).

fof(f48,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

% (17770)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f249,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))
        | ~ v1_relat_1(sK0) )
    | ~ spl2_5
    | ~ spl2_36 ),
    inference(resolution,[],[f215,f52])).

fof(f215,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X5,k2_zfmisc_1(X3,k2_relat_1(sK0)))
        | r1_xboole_0(X5,k2_zfmisc_1(X4,k2_relat_1(sK1))) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl2_36
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f210,f156,f67,f214])).

fof(f156,plain,
    ( spl2_24
  <=> ! [X1,X0] : k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f210,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X5,k2_zfmisc_1(X3,k2_relat_1(sK0)))
        | r1_xboole_0(X5,k2_zfmisc_1(X4,k2_relat_1(sK1))) )
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(superposition,[],[f68,f157])).

fof(f157,plain,
    ( ! [X0,X1] : k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl2_24
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f149,f120,f36,f156])).

fof(f36,plain,
    ( spl2_2
  <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f120,plain,
    ( spl2_18
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f149,plain,
    ( ! [X0,X1] : k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f121,f38])).

fof(f38,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f121,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl2_18
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f117,f75,f63,f120])).

fof(f75,plain,
    ( spl2_11
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f117,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) )
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(resolution,[],[f76,f64])).

fof(f76,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:17:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.40  % (17772)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.40  % (17767)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.19/0.40  % (17775)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.19/0.41  % (17775)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f369,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f53,f57,f65,f69,f77,f122,f158,f216,f254,f274,f290,f342,f349,f368])).
% 0.19/0.41  fof(f368,plain,(
% 0.19/0.41    spl2_1 | ~spl2_6 | ~spl2_60),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f367])).
% 0.19/0.41  fof(f367,plain,(
% 0.19/0.41    $false | (spl2_1 | ~spl2_6 | ~spl2_60)),
% 0.19/0.41    inference(subsumption_resolution,[],[f353,f33])).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f31])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.41  fof(f353,plain,(
% 0.19/0.41    r1_xboole_0(sK0,sK1) | (~spl2_6 | ~spl2_60)),
% 0.19/0.41    inference(resolution,[],[f348,f56])).
% 0.19/0.41  fof(f56,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.19/0.41    inference(avatar_component_clause,[],[f55])).
% 0.19/0.41  fof(f55,plain,(
% 0.19/0.41    spl2_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.41  fof(f348,plain,(
% 0.19/0.41    r1_xboole_0(sK1,sK0) | ~spl2_60),
% 0.19/0.41    inference(avatar_component_clause,[],[f346])).
% 0.19/0.41  fof(f346,plain,(
% 0.19/0.41    spl2_60 <=> r1_xboole_0(sK1,sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 0.19/0.41  fof(f349,plain,(
% 0.19/0.41    spl2_60 | ~spl2_3 | ~spl2_5 | ~spl2_59),
% 0.19/0.41    inference(avatar_split_clause,[],[f344,f340,f51,f41,f346])).
% 0.19/0.41  fof(f41,plain,(
% 0.19/0.41    spl2_3 <=> v1_relat_1(sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.41  fof(f51,plain,(
% 0.19/0.41    spl2_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.41  fof(f340,plain,(
% 0.19/0.41    spl2_59 <=> ! [X3,X2] : (~r1_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK1))) | r1_xboole_0(X3,sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.19/0.41  fof(f344,plain,(
% 0.19/0.41    r1_xboole_0(sK1,sK0) | (~spl2_3 | ~spl2_5 | ~spl2_59)),
% 0.19/0.41    inference(subsumption_resolution,[],[f343,f43])).
% 0.19/0.41  fof(f43,plain,(
% 0.19/0.41    v1_relat_1(sK1) | ~spl2_3),
% 0.19/0.41    inference(avatar_component_clause,[],[f41])).
% 0.19/0.41  fof(f343,plain,(
% 0.19/0.41    r1_xboole_0(sK1,sK0) | ~v1_relat_1(sK1) | (~spl2_5 | ~spl2_59)),
% 0.19/0.41    inference(resolution,[],[f341,f52])).
% 0.19/0.41  fof(f52,plain,(
% 0.19/0.41    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.19/0.41    inference(avatar_component_clause,[],[f51])).
% 0.19/0.41  fof(f341,plain,(
% 0.19/0.41    ( ! [X2,X3] : (~r1_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK1))) | r1_xboole_0(X3,sK0)) ) | ~spl2_59),
% 0.19/0.41    inference(avatar_component_clause,[],[f340])).
% 0.19/0.41  fof(f342,plain,(
% 0.19/0.41    spl2_59 | ~spl2_9 | ~spl2_50),
% 0.19/0.41    inference(avatar_split_clause,[],[f336,f288,f67,f340])).
% 0.19/0.41  fof(f67,plain,(
% 0.19/0.41    spl2_9 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.41  fof(f288,plain,(
% 0.19/0.41    spl2_50 <=> ! [X6] : k2_zfmisc_1(X6,k2_relat_1(sK1)) = k4_xboole_0(k2_zfmisc_1(X6,k2_relat_1(sK1)),sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.19/0.41  fof(f336,plain,(
% 0.19/0.41    ( ! [X2,X3] : (~r1_tarski(X3,k2_zfmisc_1(X2,k2_relat_1(sK1))) | r1_xboole_0(X3,sK0)) ) | (~spl2_9 | ~spl2_50)),
% 0.19/0.41    inference(superposition,[],[f68,f289])).
% 0.19/0.41  fof(f289,plain,(
% 0.19/0.41    ( ! [X6] : (k2_zfmisc_1(X6,k2_relat_1(sK1)) = k4_xboole_0(k2_zfmisc_1(X6,k2_relat_1(sK1)),sK0)) ) | ~spl2_50),
% 0.19/0.41    inference(avatar_component_clause,[],[f288])).
% 0.19/0.41  fof(f68,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl2_9),
% 0.19/0.41    inference(avatar_component_clause,[],[f67])).
% 0.19/0.41  fof(f290,plain,(
% 0.19/0.41    spl2_50 | ~spl2_8 | ~spl2_47),
% 0.19/0.41    inference(avatar_split_clause,[],[f277,f272,f63,f288])).
% 0.19/0.41  fof(f63,plain,(
% 0.19/0.41    spl2_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.41  fof(f272,plain,(
% 0.19/0.41    spl2_47 <=> ! [X7] : r1_xboole_0(k2_zfmisc_1(X7,k2_relat_1(sK1)),sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.19/0.41  fof(f277,plain,(
% 0.19/0.41    ( ! [X6] : (k2_zfmisc_1(X6,k2_relat_1(sK1)) = k4_xboole_0(k2_zfmisc_1(X6,k2_relat_1(sK1)),sK0)) ) | (~spl2_8 | ~spl2_47)),
% 0.19/0.41    inference(resolution,[],[f273,f64])).
% 0.19/0.41  fof(f64,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_8),
% 0.19/0.41    inference(avatar_component_clause,[],[f63])).
% 0.19/0.41  fof(f273,plain,(
% 0.19/0.41    ( ! [X7] : (r1_xboole_0(k2_zfmisc_1(X7,k2_relat_1(sK1)),sK0)) ) | ~spl2_47),
% 0.19/0.41    inference(avatar_component_clause,[],[f272])).
% 0.19/0.41  fof(f274,plain,(
% 0.19/0.41    spl2_47 | ~spl2_6 | ~spl2_43),
% 0.19/0.41    inference(avatar_split_clause,[],[f258,f252,f55,f272])).
% 0.19/0.41  fof(f252,plain,(
% 0.19/0.41    spl2_43 <=> ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.19/0.41  fof(f258,plain,(
% 0.19/0.41    ( ! [X7] : (r1_xboole_0(k2_zfmisc_1(X7,k2_relat_1(sK1)),sK0)) ) | (~spl2_6 | ~spl2_43)),
% 0.19/0.41    inference(resolution,[],[f253,f56])).
% 0.19/0.41  fof(f253,plain,(
% 0.19/0.41    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))) ) | ~spl2_43),
% 0.19/0.41    inference(avatar_component_clause,[],[f252])).
% 0.19/0.41  fof(f254,plain,(
% 0.19/0.41    spl2_43 | ~spl2_4 | ~spl2_5 | ~spl2_36),
% 0.19/0.41    inference(avatar_split_clause,[],[f250,f214,f51,f46,f252])).
% 0.19/0.41  fof(f46,plain,(
% 0.19/0.41    spl2_4 <=> v1_relat_1(sK0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.41  fof(f214,plain,(
% 0.19/0.41    spl2_36 <=> ! [X3,X5,X4] : (~r1_tarski(X5,k2_zfmisc_1(X3,k2_relat_1(sK0))) | r1_xboole_0(X5,k2_zfmisc_1(X4,k2_relat_1(sK1))))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.19/0.41  fof(f250,plain,(
% 0.19/0.41    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))) ) | (~spl2_4 | ~spl2_5 | ~spl2_36)),
% 0.19/0.41    inference(subsumption_resolution,[],[f249,f48])).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    v1_relat_1(sK0) | ~spl2_4),
% 0.19/0.41    inference(avatar_component_clause,[],[f46])).
% 0.19/0.41  % (17770)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.41  fof(f249,plain,(
% 0.19/0.41    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1))) | ~v1_relat_1(sK0)) ) | (~spl2_5 | ~spl2_36)),
% 0.19/0.41    inference(resolution,[],[f215,f52])).
% 0.19/0.41  fof(f215,plain,(
% 0.19/0.41    ( ! [X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(X3,k2_relat_1(sK0))) | r1_xboole_0(X5,k2_zfmisc_1(X4,k2_relat_1(sK1)))) ) | ~spl2_36),
% 0.19/0.41    inference(avatar_component_clause,[],[f214])).
% 0.19/0.41  fof(f216,plain,(
% 0.19/0.41    spl2_36 | ~spl2_9 | ~spl2_24),
% 0.19/0.41    inference(avatar_split_clause,[],[f210,f156,f67,f214])).
% 0.19/0.41  fof(f156,plain,(
% 0.19/0.41    spl2_24 <=> ! [X1,X0] : k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.19/0.41  fof(f210,plain,(
% 0.19/0.41    ( ! [X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(X3,k2_relat_1(sK0))) | r1_xboole_0(X5,k2_zfmisc_1(X4,k2_relat_1(sK1)))) ) | (~spl2_9 | ~spl2_24)),
% 0.19/0.41    inference(superposition,[],[f68,f157])).
% 0.19/0.41  fof(f157,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1)))) ) | ~spl2_24),
% 0.19/0.41    inference(avatar_component_clause,[],[f156])).
% 0.19/0.41  fof(f158,plain,(
% 0.19/0.41    spl2_24 | ~spl2_2 | ~spl2_18),
% 0.19/0.41    inference(avatar_split_clause,[],[f149,f120,f36,f156])).
% 0.19/0.41  fof(f36,plain,(
% 0.19/0.41    spl2_2 <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.41  fof(f120,plain,(
% 0.19/0.41    spl2_18 <=> ! [X1,X3,X0,X2] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.19/0.41  fof(f149,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1)))) ) | (~spl2_2 | ~spl2_18)),
% 0.19/0.41    inference(resolution,[],[f121,f38])).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl2_2),
% 0.19/0.41    inference(avatar_component_clause,[],[f36])).
% 0.19/0.41  fof(f121,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) ) | ~spl2_18),
% 0.19/0.41    inference(avatar_component_clause,[],[f120])).
% 0.19/0.41  fof(f122,plain,(
% 0.19/0.41    spl2_18 | ~spl2_8 | ~spl2_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f117,f75,f63,f120])).
% 0.19/0.41  fof(f75,plain,(
% 0.19/0.41    spl2_11 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.19/0.41  fof(f117,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) ) | (~spl2_8 | ~spl2_11)),
% 0.19/0.41    inference(resolution,[],[f76,f64])).
% 0.19/0.41  fof(f76,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) ) | ~spl2_11),
% 0.19/0.41    inference(avatar_component_clause,[],[f75])).
% 0.19/0.41  fof(f77,plain,(
% 0.19/0.41    spl2_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f29,f75])).
% 0.19/0.41  fof(f29,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.41    inference(ennf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.19/0.41  fof(f69,plain,(
% 0.19/0.41    spl2_9),
% 0.19/0.41    inference(avatar_split_clause,[],[f27,f67])).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.41    inference(ennf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.19/0.41  fof(f65,plain,(
% 0.19/0.41    spl2_8),
% 0.19/0.41    inference(avatar_split_clause,[],[f24,f63])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.41    inference(nnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.41  fof(f57,plain,(
% 0.19/0.41    spl2_6),
% 0.19/0.41    inference(avatar_split_clause,[],[f23,f55])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.41  fof(f53,plain,(
% 0.19/0.41    spl2_5),
% 0.19/0.41    inference(avatar_split_clause,[],[f22,f51])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    spl2_4),
% 0.19/0.41    inference(avatar_split_clause,[],[f18,f46])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    v1_relat_1(sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.41    inference(flattening,[],[f8])).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,negated_conjecture,(
% 0.19/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.19/0.41    inference(negated_conjecture,[],[f6])).
% 0.19/0.41  fof(f6,conjecture,(
% 0.19/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).
% 0.19/0.41  fof(f44,plain,(
% 0.19/0.41    spl2_3),
% 0.19/0.41    inference(avatar_split_clause,[],[f19,f41])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    v1_relat_1(sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f39,plain,(
% 0.19/0.41    spl2_2),
% 0.19/0.41    inference(avatar_split_clause,[],[f20,f36])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f34,plain,(
% 0.19/0.41    ~spl2_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f21,f31])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ~r1_xboole_0(sK0,sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (17775)------------------------------
% 0.19/0.41  % (17775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (17775)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (17775)Memory used [KB]: 6268
% 0.19/0.41  % (17775)Time elapsed: 0.010 s
% 0.19/0.41  % (17775)------------------------------
% 0.19/0.41  % (17775)------------------------------
% 0.19/0.41  % (17764)Success in time 0.072 s
%------------------------------------------------------------------------------
