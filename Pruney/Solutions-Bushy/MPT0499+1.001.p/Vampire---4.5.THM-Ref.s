%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0499+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 117 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  191 ( 305 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f45,f49,f53,f61,f65,f77,f93,f123,f129,f140,f155,f168])).

fof(f168,plain,
    ( spl2_1
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl2_1
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f159,f30])).

fof(f30,plain,
    ( sK1 != k7_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> sK1 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f159,plain,
    ( sK1 = k7_relat_1(sK1,sK0)
    | ~ spl2_23
    | ~ spl2_26 ),
    inference(superposition,[],[f139,f154])).

fof(f154,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,k2_relat_1(sK1)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_26
  <=> ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f139,plain,
    ( sK1 = k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl2_23
  <=> sK1 = k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f155,plain,
    ( spl2_26
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f151,f47,f38,f153])).

fof(f38,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f151,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f140,plain,
    ( spl2_23
    | ~ spl2_6
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f131,f126,f51,f137])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f126,plain,
    ( spl2_21
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f131,plain,
    ( sK1 = k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl2_6
    | ~ spl2_21 ),
    inference(resolution,[],[f128,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f128,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f126])).

fof(f129,plain,
    ( spl2_21
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f124,f121,f33,f126])).

fof(f33,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f121,plain,
    ( spl2_20
  <=> ! [X1] :
        ( r1_tarski(sK1,k2_zfmisc_1(X1,k2_relat_1(sK1)))
        | ~ r1_tarski(k1_relat_1(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f124,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(resolution,[],[f122,f35])).

fof(f35,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f122,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK1),X1)
        | r1_tarski(sK1,k2_zfmisc_1(X1,k2_relat_1(sK1))) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl2_20
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f115,f91,f59,f121])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f91,plain,
    ( spl2_14
  <=> ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X1)
        | r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f115,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,k2_zfmisc_1(X1,k2_relat_1(sK1)))
        | ~ r1_tarski(k1_relat_1(sK1),X1) )
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl2_14
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f85,f74,f63,f91])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f74,plain,
    ( spl2_11
  <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f85,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X1)
        | r1_tarski(sK1,X1) )
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(resolution,[],[f64,f76])).

fof(f76,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f77,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f72,f43,f38,f74])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f72,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f44,f40])).

fof(f44,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k7_relat_1(sK1,sK0)
    & r1_tarski(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != X1
        & r1_tarski(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( sK1 != k7_relat_1(sK1,sK0)
      & r1_tarski(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k7_relat_1(X1,X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f28])).

fof(f20,plain,(
    sK1 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
