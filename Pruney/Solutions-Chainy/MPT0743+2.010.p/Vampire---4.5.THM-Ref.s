%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 222 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  306 ( 759 expanded)
%              Number of equality atoms :   28 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f73,f96,f99,f137,f152,f165,f187])).

fof(f187,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f184,f74])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f51,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f184,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f66,f177])).

fof(f177,plain,
    ( sK0 = sK1
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f175,f168])).

fof(f168,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f175,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f171,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f38,f41,f37])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f171,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f170,f90])).

fof(f90,plain,
    ( v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_3
  <=> v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f170,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f169,f34])).

fof(f34,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

% (15999)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (16009)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f169,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | spl2_2 ),
    inference(resolution,[],[f71,f40])).

% (16007)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (15997)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (16025)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (16018)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (16010)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f71,plain,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_2
  <=> r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f165,plain,
    ( ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f109,f136])).

fof(f136,plain,
    ( sK0 = sK1
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f109,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ spl2_4 ),
    inference(resolution,[],[f95,f51])).

fof(f95,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_4
  <=> r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f152,plain,
    ( spl2_1
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl2_1
    | spl2_7 ),
    inference(subsumption_resolution,[],[f150,f67])).

fof(f67,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f150,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_7 ),
    inference(subsumption_resolution,[],[f149,f34])).

fof(f149,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | spl2_7 ),
    inference(subsumption_resolution,[],[f146,f33])).

fof(f33,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | spl2_7 ),
    inference(resolution,[],[f86,f132])).

fof(f132,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_7
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f137,plain,
    ( ~ spl2_7
    | spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f125,f93,f134,f130])).

fof(f125,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

% (16023)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (16021)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f99,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f97,f33])).

fof(f97,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_3 ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f39,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f91,plain,
    ( ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f87,f69,f93,f89])).

fof(f87,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ spl2_2 ),
    inference(resolution,[],[f43,f70])).

fof(f70,plain,
    ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f73,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f55,f69,f65])).

fof(f55,plain,
    ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f35,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f54,f69,f65])).

fof(f54,plain,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f36,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (15998)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (16004)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (16005)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (16002)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (16002)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (16011)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (16008)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (16015)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (16013)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (16019)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f72,f73,f96,f99,f137,f152,f165,f187])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~spl2_1 | spl2_2 | ~spl2_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    $false | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f51,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    r2_hidden(sK0,sK0) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(backward_demodulation,[],[f66,f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    sK0 = sK1 | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f175,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | ~spl2_1),
% 0.21/0.53    inference(resolution,[],[f66,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | sK0 = sK1 | (spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(resolution,[],[f171,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f41,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | (spl2_2 | ~spl2_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f170,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl2_3 <=> v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | ~v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v3_ordinal1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  % (15999)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  % (16009)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | spl2_2),
% 0.21/0.53    inference(resolution,[],[f71,f40])).
% 0.21/0.54  % (16007)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (15997)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (16025)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (16018)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (16010)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl2_2 <=> r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 1.43/0.54  fof(f65,plain,(
% 1.43/0.54    spl2_1 <=> r2_hidden(sK0,sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.43/0.54  fof(f165,plain,(
% 1.43/0.54    ~spl2_4 | ~spl2_8),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f164])).
% 1.43/0.54  fof(f164,plain,(
% 1.43/0.54    $false | (~spl2_4 | ~spl2_8)),
% 1.43/0.54    inference(subsumption_resolution,[],[f160,f63])).
% 1.43/0.54  fof(f63,plain,(
% 1.43/0.54    ( ! [X1] : (r2_hidden(X1,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))) )),
% 1.43/0.54    inference(equality_resolution,[],[f57])).
% 1.43/0.54  fof(f57,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) | X0 != X1) )),
% 1.43/0.54    inference(definition_unfolding,[],[f50,f53])).
% 1.43/0.54  fof(f50,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f32])).
% 1.43/0.54  fof(f160,plain,(
% 1.43/0.54    ~r2_hidden(sK0,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | (~spl2_4 | ~spl2_8)),
% 1.43/0.54    inference(backward_demodulation,[],[f109,f136])).
% 1.43/0.54  fof(f136,plain,(
% 1.43/0.54    sK0 = sK1 | ~spl2_8),
% 1.43/0.54    inference(avatar_component_clause,[],[f134])).
% 1.43/0.54  fof(f134,plain,(
% 1.43/0.54    spl2_8 <=> sK0 = sK1),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.43/0.54  fof(f109,plain,(
% 1.43/0.54    ~r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | ~spl2_4),
% 1.43/0.54    inference(resolution,[],[f95,f51])).
% 1.43/0.54  fof(f95,plain,(
% 1.43/0.54    r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | ~spl2_4),
% 1.43/0.54    inference(avatar_component_clause,[],[f93])).
% 1.43/0.54  fof(f93,plain,(
% 1.43/0.54    spl2_4 <=> r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.43/0.54  fof(f152,plain,(
% 1.43/0.54    spl2_1 | spl2_7),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f151])).
% 1.43/0.54  fof(f151,plain,(
% 1.43/0.54    $false | (spl2_1 | spl2_7)),
% 1.43/0.54    inference(subsumption_resolution,[],[f150,f67])).
% 1.43/0.54  fof(f67,plain,(
% 1.43/0.54    ~r2_hidden(sK0,sK1) | spl2_1),
% 1.43/0.54    inference(avatar_component_clause,[],[f65])).
% 1.43/0.54  fof(f150,plain,(
% 1.43/0.54    r2_hidden(sK0,sK1) | spl2_7),
% 1.43/0.54    inference(subsumption_resolution,[],[f149,f34])).
% 1.43/0.54  fof(f149,plain,(
% 1.43/0.54    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | spl2_7),
% 1.43/0.54    inference(subsumption_resolution,[],[f146,f33])).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    v3_ordinal1(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f27])).
% 1.43/0.54  fof(f146,plain,(
% 1.43/0.54    ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | spl2_7),
% 1.43/0.54    inference(resolution,[],[f86,f132])).
% 1.43/0.54  fof(f132,plain,(
% 1.43/0.54    ~r1_tarski(sK1,sK0) | spl2_7),
% 1.43/0.54    inference(avatar_component_clause,[],[f130])).
% 1.43/0.54  fof(f130,plain,(
% 1.43/0.54    spl2_7 <=> r1_tarski(sK1,sK0)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.43/0.54  fof(f86,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 1.43/0.54    inference(duplicate_literal_removal,[],[f85])).
% 1.43/0.54  fof(f85,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.54    inference(resolution,[],[f43,f40])).
% 1.43/0.54  fof(f43,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f28])).
% 1.43/0.54  fof(f28,plain,(
% 1.43/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(nnf_transformation,[],[f20])).
% 1.43/0.54  fof(f20,plain,(
% 1.43/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(flattening,[],[f19])).
% 1.43/0.54  fof(f19,plain,(
% 1.43/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f7])).
% 1.43/0.54  fof(f7,axiom,(
% 1.43/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.43/0.54  fof(f137,plain,(
% 1.43/0.54    ~spl2_7 | spl2_8 | ~spl2_4),
% 1.43/0.54    inference(avatar_split_clause,[],[f125,f93,f134,f130])).
% 1.43/0.54  fof(f125,plain,(
% 1.43/0.54    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl2_4),
% 1.43/0.54    inference(resolution,[],[f106,f47])).
% 1.43/0.54  fof(f47,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f30])).
% 1.43/0.54  fof(f106,plain,(
% 1.43/0.54    r1_tarski(sK0,sK1) | ~spl2_4),
% 1.43/0.54    inference(resolution,[],[f95,f60])).
% 1.43/0.54  fof(f60,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.43/0.54    inference(definition_unfolding,[],[f52,f41])).
% 1.43/0.54  fof(f52,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f22])).
% 1.43/0.54  % (16023)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.54  % (16021)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.43/0.54    inference(ennf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.43/0.54  fof(f99,plain,(
% 1.43/0.54    spl2_3),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f98])).
% 1.43/0.54  fof(f98,plain,(
% 1.43/0.54    $false | spl2_3),
% 1.43/0.54    inference(subsumption_resolution,[],[f97,f33])).
% 1.43/0.54  fof(f97,plain,(
% 1.43/0.54    ~v3_ordinal1(sK0) | spl2_3),
% 1.43/0.54    inference(resolution,[],[f91,f56])).
% 1.43/0.54  fof(f56,plain,(
% 1.43/0.54    ( ! [X0] : (v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) | ~v3_ordinal1(X0)) )),
% 1.43/0.54    inference(definition_unfolding,[],[f39,f53])).
% 1.43/0.54  fof(f39,plain,(
% 1.43/0.54    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f15,plain,(
% 1.43/0.54    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f10])).
% 1.43/0.54  fof(f10,axiom,(
% 1.43/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.43/0.54  fof(f91,plain,(
% 1.43/0.54    ~v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | spl2_3),
% 1.43/0.54    inference(avatar_component_clause,[],[f89])).
% 1.43/0.54  fof(f96,plain,(
% 1.43/0.54    ~spl2_3 | spl2_4 | ~spl2_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f87,f69,f93,f89])).
% 1.43/0.54  fof(f87,plain,(
% 1.43/0.54    r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | ~v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | ~spl2_2),
% 1.43/0.54    inference(subsumption_resolution,[],[f84,f34])).
% 1.43/0.54  fof(f84,plain,(
% 1.43/0.54    r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) | ~spl2_2),
% 1.43/0.54    inference(resolution,[],[f43,f70])).
% 1.43/0.54  fof(f70,plain,(
% 1.43/0.54    r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | ~spl2_2),
% 1.43/0.54    inference(avatar_component_clause,[],[f69])).
% 1.43/0.54  fof(f73,plain,(
% 1.43/0.54    spl2_1 | spl2_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f55,f69,f65])).
% 1.43/0.54  fof(f55,plain,(
% 1.43/0.54    r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 1.43/0.54    inference(definition_unfolding,[],[f35,f53])).
% 1.43/0.54  fof(f35,plain,(
% 1.43/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f27])).
% 1.43/0.54  fof(f72,plain,(
% 1.43/0.54    ~spl2_1 | ~spl2_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f54,f69,f65])).
% 1.43/0.54  fof(f54,plain,(
% 1.43/0.54    ~r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 1.43/0.54    inference(definition_unfolding,[],[f36,f53])).
% 1.43/0.54  fof(f36,plain,(
% 1.43/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f27])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (16002)------------------------------
% 1.43/0.54  % (16002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (16002)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (16002)Memory used [KB]: 10746
% 1.43/0.54  % (16002)Time elapsed: 0.116 s
% 1.43/0.54  % (16002)------------------------------
% 1.43/0.54  % (16002)------------------------------
% 1.43/0.54  % (16013)Refutation not found, incomplete strategy% (16013)------------------------------
% 1.43/0.54  % (16013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (16013)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (16013)Memory used [KB]: 1663
% 1.43/0.54  % (16013)Time elapsed: 0.126 s
% 1.43/0.54  % (16013)------------------------------
% 1.43/0.54  % (16013)------------------------------
% 1.43/0.54  % (15995)Success in time 0.187 s
%------------------------------------------------------------------------------
