%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 358 expanded)
%              Number of leaves         :   21 ( 114 expanded)
%              Depth                    :   23
%              Number of atoms          :  447 (1706 expanded)
%              Number of equality atoms :  133 ( 604 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f113,f142,f155,f245,f257,f258,f348,f360,f364])).

fof(f364,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f362,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f362,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f84,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f84,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_3
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f360,plain,
    ( ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f69,f150])).

fof(f150,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_4 ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_4
  <=> ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f348,plain,
    ( spl7_1
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl7_1
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f307,f141])).

fof(f141,plain,
    ( ! [X2,X1] : X1 = X2
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_8
  <=> ! [X1,X2] : X1 = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f307,plain,
    ( ! [X0] : k1_xboole_0 != X0
    | spl7_1
    | ~ spl7_8 ),
    inference(superposition,[],[f65,f141])).

fof(f65,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f258,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f196,f104,f101])).

fof(f101,plain,
    ( spl7_5
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | k1_xboole_0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f104,plain,
    ( spl7_6
  <=> ! [X1] : r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f196,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X5,X3)
      | k1_xboole_0 != X3 ) ),
    inference(superposition,[],[f98,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_relat_1(sK6(X0,X1))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f75,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(sK6(X0,X1))
      | k1_xboole_0 = k2_relat_1(sK6(X0,X1)) ) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f95,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(sK6(X1,X2),X0),k2_relat_1(sK6(X1,X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f94,f54])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6(X1,X2)))
      | r2_hidden(k1_funct_1(sK6(X1,X2),X0),k2_relat_1(sK6(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f93,f52])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6(X1,X2)))
      | r2_hidden(k1_funct_1(sK6(X1,X2),X0),k2_relat_1(sK6(X1,X2)))
      | ~ v1_relat_1(sK6(X1,X2)) ) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f257,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f256,f86,f82])).

fof(f256,plain,(
    ! [X10] :
      ( sK1 != X10
      | ~ r1_tarski(k1_xboole_0,sK0)
      | k1_xboole_0 != X10 ) ),
    inference(forward_demodulation,[],[f255,f54])).

fof(f255,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | sK1 != k1_relat_1(sK6(X10,X11))
      | k1_xboole_0 != X10 ) ),
    inference(subsumption_resolution,[],[f254,f52])).

fof(f254,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | sK1 != k1_relat_1(sK6(X10,X11))
      | ~ v1_relat_1(sK6(X10,X11))
      | k1_xboole_0 != X10 ) ),
    inference(subsumption_resolution,[],[f198,f53])).

fof(f198,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | sK1 != k1_relat_1(sK6(X10,X11))
      | ~ v1_funct_1(sK6(X10,X11))
      | ~ v1_relat_1(sK6(X10,X11))
      | k1_xboole_0 != X10 ) ),
    inference(superposition,[],[f36,f76])).

fof(f36,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

% (16690)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (16691)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (16691)Refutation not found, incomplete strategy% (16691)------------------------------
% (16691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16691)Termination reason: Refutation not found, incomplete strategy

% (16691)Memory used [KB]: 10618
% (16691)Time elapsed: 0.118 s
% (16691)------------------------------
% (16691)------------------------------
% (16688)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (16697)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (16680)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (16678)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (16698)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

% (16686)Termination reason: Refutation not found, incomplete strategy
fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

% (16686)Memory used [KB]: 10618
% (16686)Time elapsed: 0.121 s
% (16686)------------------------------
% (16686)------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

% (16676)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f245,plain,
    ( spl7_1
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl7_1
    | ~ spl7_3 ),
    inference(equality_resolution,[],[f243])).

fof(f243,plain,
    ( ! [X0] : sK1 != X0
    | spl7_1
    | ~ spl7_3 ),
    inference(superposition,[],[f242,f54])).

fof(f242,plain,
    ( ! [X0] : sK1 != k1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0)))
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f241,f52])).

fof(f241,plain,
    ( ! [X0] :
        ( sK1 != k1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0)))
        | ~ v1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0))) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f236,f53])).

fof(f236,plain,
    ( ! [X0] :
        ( sK1 != k1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0)))
        | ~ v1_funct_1(sK6(X0,sK5(sK0,k1_xboole_0)))
        | ~ v1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0))) )
    | spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f235,f36])).

fof(f235,plain,
    ( ! [X22] : r1_tarski(k2_relat_1(sK6(X22,sK5(sK0,k1_xboole_0))),sK0)
    | spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f227,f149])).

fof(f149,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f148,f65])).

fof(f148,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl7_3 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f227,plain,(
    ! [X21,X19,X20] :
      ( r1_tarski(X20,X21)
      | r1_tarski(k2_relat_1(sK6(X19,sK5(X20,X21))),X20) ) ),
    inference(resolution,[],[f221,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_relat_1(sK6(X0,X1)),X2) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_relat_1(sK6(X0,X1)),X2)
      | r1_tarski(k2_relat_1(sK6(X0,X1)),X2) ) ),
    inference(superposition,[],[f51,f133])).

fof(f133,plain,(
    ! [X14,X15,X16] :
      ( sK5(k2_relat_1(sK6(X15,X14)),X16) = X14
      | r1_tarski(k2_relat_1(sK6(X15,X14)),X16) ) ),
    inference(resolution,[],[f127,f50])).

fof(f127,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_relat_1(sK6(X3,X4)))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f124,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f120,f52])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK6(X0,X1),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(superposition,[],[f59,f54])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

% (16669)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( X4 = X5
      | ~ r2_hidden(X5,k2_relat_1(sK6(X3,X4)))
      | ~ r2_hidden(sK4(sK6(X3,X4),X5),X3) ) ),
    inference(superposition,[],[f123,f55])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(sK6(X1,X2),sK4(sK6(X1,X2),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(sK6(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f122,f52])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK6(X1,X2)))
      | k1_funct_1(sK6(X1,X2),sK4(sK6(X1,X2),X0)) = X0
      | ~ v1_relat_1(sK6(X1,X2)) ) ),
    inference(resolution,[],[f58,f53])).

fof(f58,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f155,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl7_7 ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,
    ( ! [X0] : k1_xboole_0 != X0
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_7
  <=> ! [X0] : k1_xboole_0 != X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f142,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f135,f104,f140,f137])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( X1 = X2
        | k1_xboole_0 != X0 )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f134,f105])).

fof(f105,plain,
    ( ! [X1] : r2_hidden(X1,k1_xboole_0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | X1 = X2
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f127,f76])).

fof(f113,plain,
    ( spl7_3
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f108,f84])).

fof(f108,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_5 ),
    inference(resolution,[],[f107,f50])).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_5 ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,
    ( ! [X2,X0] :
        ( k1_xboole_0 != X0
        | ~ r2_hidden(X2,X0) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f70,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f35,f67,f63])).

fof(f35,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:57:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (16670)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (16677)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (16672)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (16696)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (16693)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (16685)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (16673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16681)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (16687)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (16679)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (16699)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (16679)Refutation not found, incomplete strategy% (16679)------------------------------
% 0.21/0.51  % (16679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16679)Memory used [KB]: 10618
% 0.21/0.51  % (16679)Time elapsed: 0.108 s
% 0.21/0.51  % (16679)------------------------------
% 0.21/0.51  % (16679)------------------------------
% 0.21/0.51  % (16675)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (16671)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16674)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16671)Refutation not found, incomplete strategy% (16671)------------------------------
% 0.21/0.51  % (16671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16671)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16671)Memory used [KB]: 10618
% 0.21/0.51  % (16671)Time elapsed: 0.099 s
% 0.21/0.51  % (16671)------------------------------
% 0.21/0.51  % (16671)------------------------------
% 0.21/0.52  % (16672)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (16682)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (16677)Refutation not found, incomplete strategy% (16677)------------------------------
% 0.21/0.52  % (16677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16677)Memory used [KB]: 10618
% 0.21/0.52  % (16677)Time elapsed: 0.131 s
% 0.21/0.52  % (16677)------------------------------
% 0.21/0.52  % (16677)------------------------------
% 0.21/0.52  % (16694)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (16683)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.52  % (16686)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.53  % (16686)Refutation not found, incomplete strategy% (16686)------------------------------
% 1.28/0.53  % (16686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f365,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f70,f113,f142,f155,f245,f257,f258,f348,f360,f364])).
% 1.28/0.53  fof(f364,plain,(
% 1.28/0.53    ~spl7_1 | spl7_3),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f363])).
% 1.28/0.53  fof(f363,plain,(
% 1.28/0.53    $false | (~spl7_1 | spl7_3)),
% 1.28/0.53    inference(subsumption_resolution,[],[f362,f60])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.28/0.53    inference(equality_resolution,[],[f47])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.53    inference(flattening,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.53    inference(nnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.53  fof(f362,plain,(
% 1.28/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_1 | spl7_3)),
% 1.28/0.53    inference(forward_demodulation,[],[f84,f64])).
% 1.28/0.53  fof(f64,plain,(
% 1.28/0.53    k1_xboole_0 = sK0 | ~spl7_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f63])).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    spl7_1 <=> k1_xboole_0 = sK0),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    ~r1_tarski(k1_xboole_0,sK0) | spl7_3),
% 1.28/0.53    inference(avatar_component_clause,[],[f82])).
% 1.28/0.53  fof(f82,plain,(
% 1.28/0.53    spl7_3 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.28/0.53  fof(f360,plain,(
% 1.28/0.53    ~spl7_2 | ~spl7_4),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f359])).
% 1.28/0.53  fof(f359,plain,(
% 1.28/0.53    $false | (~spl7_2 | ~spl7_4)),
% 1.28/0.53    inference(subsumption_resolution,[],[f69,f150])).
% 1.28/0.53  fof(f150,plain,(
% 1.28/0.53    k1_xboole_0 != sK1 | ~spl7_4),
% 1.28/0.53    inference(equality_resolution,[],[f87])).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) ) | ~spl7_4),
% 1.28/0.53    inference(avatar_component_clause,[],[f86])).
% 1.28/0.53  fof(f86,plain,(
% 1.28/0.53    spl7_4 <=> ! [X0] : (sK1 != X0 | k1_xboole_0 != X0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    k1_xboole_0 = sK1 | ~spl7_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f67])).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.28/0.53  fof(f348,plain,(
% 1.28/0.53    spl7_1 | ~spl7_8),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f347])).
% 1.28/0.53  fof(f347,plain,(
% 1.28/0.53    $false | (spl7_1 | ~spl7_8)),
% 1.28/0.53    inference(subsumption_resolution,[],[f307,f141])).
% 1.28/0.53  fof(f141,plain,(
% 1.28/0.53    ( ! [X2,X1] : (X1 = X2) ) | ~spl7_8),
% 1.28/0.53    inference(avatar_component_clause,[],[f140])).
% 1.28/0.53  fof(f140,plain,(
% 1.28/0.53    spl7_8 <=> ! [X1,X2] : X1 = X2),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.28/0.53  fof(f307,plain,(
% 1.28/0.53    ( ! [X0] : (k1_xboole_0 != X0) ) | (spl7_1 | ~spl7_8)),
% 1.28/0.53    inference(superposition,[],[f65,f141])).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    k1_xboole_0 != sK0 | spl7_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f63])).
% 1.28/0.53  fof(f258,plain,(
% 1.28/0.53    spl7_5 | spl7_6),
% 1.28/0.53    inference(avatar_split_clause,[],[f196,f104,f101])).
% 1.28/0.53  fof(f101,plain,(
% 1.28/0.53    spl7_5 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | k1_xboole_0 != X0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.28/0.53  fof(f104,plain,(
% 1.28/0.53    spl7_6 <=> ! [X1] : r2_hidden(X1,k1_xboole_0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.28/0.53  fof(f196,plain,(
% 1.28/0.53    ( ! [X4,X5,X3] : (r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X5,X3) | k1_xboole_0 != X3) )),
% 1.28/0.53    inference(superposition,[],[f98,f76])).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_relat_1(sK6(X0,X1)) | k1_xboole_0 != X0) )),
% 1.28/0.53    inference(forward_demodulation,[],[f75,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.28/0.53    inference(ennf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.28/0.53  fof(f75,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK6(X0,X1)) | k1_xboole_0 = k2_relat_1(sK6(X0,X1))) )),
% 1.28/0.53    inference(resolution,[],[f37,f52])).
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = k2_relat_1(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.28/0.53    inference(nnf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.28/0.53  fof(f98,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0)) )),
% 1.28/0.53    inference(duplicate_literal_removal,[],[f96])).
% 1.28/0.53  fof(f96,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0) | ~r2_hidden(X2,X0)) )),
% 1.28/0.53    inference(superposition,[],[f95,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f95,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(sK6(X1,X2),X0),k2_relat_1(sK6(X1,X2))) | ~r2_hidden(X0,X1)) )),
% 1.28/0.53    inference(forward_demodulation,[],[f94,f54])).
% 1.28/0.53  fof(f94,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(sK6(X1,X2))) | r2_hidden(k1_funct_1(sK6(X1,X2),X0),k2_relat_1(sK6(X1,X2)))) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f93,f52])).
% 1.28/0.53  fof(f93,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(sK6(X1,X2))) | r2_hidden(k1_funct_1(sK6(X1,X2),X0),k2_relat_1(sK6(X1,X2))) | ~v1_relat_1(sK6(X1,X2))) )),
% 1.28/0.53    inference(resolution,[],[f45,f53])).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(flattening,[],[f14])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.28/0.53    inference(ennf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.28/0.53  fof(f257,plain,(
% 1.28/0.53    ~spl7_3 | spl7_4),
% 1.28/0.53    inference(avatar_split_clause,[],[f256,f86,f82])).
% 1.28/0.53  fof(f256,plain,(
% 1.28/0.53    ( ! [X10] : (sK1 != X10 | ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != X10) )),
% 1.28/0.53    inference(forward_demodulation,[],[f255,f54])).
% 1.28/0.53  fof(f255,plain,(
% 1.28/0.53    ( ! [X10,X11] : (~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(sK6(X10,X11)) | k1_xboole_0 != X10) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f254,f52])).
% 1.28/0.53  fof(f254,plain,(
% 1.28/0.53    ( ! [X10,X11] : (~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(sK6(X10,X11)) | ~v1_relat_1(sK6(X10,X11)) | k1_xboole_0 != X10) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f198,f53])).
% 1.28/0.53  fof(f198,plain,(
% 1.28/0.53    ( ! [X10,X11] : (~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(sK6(X10,X11)) | ~v1_funct_1(sK6(X10,X11)) | ~v1_relat_1(sK6(X10,X11)) | k1_xboole_0 != X10) )),
% 1.28/0.53    inference(superposition,[],[f36,f76])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  % (16690)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.53  % (16691)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (16691)Refutation not found, incomplete strategy% (16691)------------------------------
% 1.28/0.53  % (16691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (16691)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (16691)Memory used [KB]: 10618
% 1.28/0.53  % (16691)Time elapsed: 0.118 s
% 1.28/0.53  % (16691)------------------------------
% 1.28/0.53  % (16691)------------------------------
% 1.28/0.53  % (16688)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.53  % (16697)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.53  % (16680)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.53  % (16678)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (16698)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.53  fof(f10,plain,(
% 1.28/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.28/0.53    inference(flattening,[],[f9])).
% 1.28/0.53  fof(f9,plain,(
% 1.28/0.53    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f8])).
% 1.28/0.53  % (16686)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  fof(f8,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.28/0.53    inference(negated_conjecture,[],[f7])).
% 1.28/0.53  
% 1.28/0.53  % (16686)Memory used [KB]: 10618
% 1.28/0.53  % (16686)Time elapsed: 0.121 s
% 1.28/0.53  % (16686)------------------------------
% 1.28/0.53  % (16686)------------------------------
% 1.28/0.53  fof(f7,conjecture,(
% 1.28/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.28/0.54  % (16676)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.54  fof(f245,plain,(
% 1.28/0.54    spl7_1 | ~spl7_3),
% 1.28/0.54    inference(avatar_contradiction_clause,[],[f244])).
% 1.28/0.54  fof(f244,plain,(
% 1.28/0.54    $false | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(equality_resolution,[],[f243])).
% 1.28/0.54  fof(f243,plain,(
% 1.28/0.54    ( ! [X0] : (sK1 != X0) ) | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(superposition,[],[f242,f54])).
% 1.28/0.54  fof(f242,plain,(
% 1.28/0.54    ( ! [X0] : (sK1 != k1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0)))) ) | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(subsumption_resolution,[],[f241,f52])).
% 1.28/0.54  fof(f241,plain,(
% 1.28/0.54    ( ! [X0] : (sK1 != k1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0))) | ~v1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0)))) ) | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(subsumption_resolution,[],[f236,f53])).
% 1.28/0.54  fof(f236,plain,(
% 1.28/0.54    ( ! [X0] : (sK1 != k1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0))) | ~v1_funct_1(sK6(X0,sK5(sK0,k1_xboole_0))) | ~v1_relat_1(sK6(X0,sK5(sK0,k1_xboole_0)))) ) | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(resolution,[],[f235,f36])).
% 1.28/0.54  fof(f235,plain,(
% 1.28/0.54    ( ! [X22] : (r1_tarski(k2_relat_1(sK6(X22,sK5(sK0,k1_xboole_0))),sK0)) ) | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(resolution,[],[f227,f149])).
% 1.28/0.54  fof(f149,plain,(
% 1.28/0.54    ~r1_tarski(sK0,k1_xboole_0) | (spl7_1 | ~spl7_3)),
% 1.28/0.54    inference(subsumption_resolution,[],[f148,f65])).
% 1.28/0.54  fof(f148,plain,(
% 1.28/0.54    k1_xboole_0 = sK0 | ~r1_tarski(sK0,k1_xboole_0) | ~spl7_3),
% 1.28/0.54    inference(resolution,[],[f83,f48])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f28])).
% 1.28/0.54  fof(f83,plain,(
% 1.28/0.54    r1_tarski(k1_xboole_0,sK0) | ~spl7_3),
% 1.28/0.54    inference(avatar_component_clause,[],[f82])).
% 1.28/0.54  fof(f227,plain,(
% 1.28/0.54    ( ! [X21,X19,X20] : (r1_tarski(X20,X21) | r1_tarski(k2_relat_1(sK6(X19,sK5(X20,X21))),X20)) )),
% 1.28/0.54    inference(resolution,[],[f221,f50])).
% 1.28/0.54  fof(f50,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f32])).
% 1.28/0.54  fof(f32,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(rectify,[],[f29])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(nnf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.54  fof(f221,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_relat_1(sK6(X0,X1)),X2)) )),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f218])).
% 1.28/0.54  fof(f218,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_relat_1(sK6(X0,X1)),X2) | r1_tarski(k2_relat_1(sK6(X0,X1)),X2)) )),
% 1.28/0.54    inference(superposition,[],[f51,f133])).
% 1.28/0.54  fof(f133,plain,(
% 1.28/0.54    ( ! [X14,X15,X16] : (sK5(k2_relat_1(sK6(X15,X14)),X16) = X14 | r1_tarski(k2_relat_1(sK6(X15,X14)),X16)) )),
% 1.28/0.54    inference(resolution,[],[f127,f50])).
% 1.28/0.54  fof(f127,plain,(
% 1.28/0.54    ( ! [X4,X5,X3] : (~r2_hidden(X5,k2_relat_1(sK6(X3,X4))) | X4 = X5) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f124,f121])).
% 1.28/0.54  fof(f121,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1)))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f120,f52])).
% 1.28/0.54  fof(f120,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_relat_1(sK6(X0,X1))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f119,f53])).
% 1.28/0.54  fof(f119,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK6(X0,X1),X2),X0) | ~r2_hidden(X2,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1))) )),
% 1.28/0.54    inference(superposition,[],[f59,f54])).
% 1.28/0.54  fof(f59,plain,(
% 1.28/0.54    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.54    inference(equality_resolution,[],[f39])).
% 1.28/0.54  fof(f39,plain,(
% 1.28/0.54    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(rectify,[],[f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(nnf_transformation,[],[f13])).
% 1.28/0.54  % (16669)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.54  fof(f13,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(flattening,[],[f12])).
% 1.28/0.54  fof(f12,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.28/0.54  fof(f124,plain,(
% 1.28/0.54    ( ! [X4,X5,X3] : (X4 = X5 | ~r2_hidden(X5,k2_relat_1(sK6(X3,X4))) | ~r2_hidden(sK4(sK6(X3,X4),X5),X3)) )),
% 1.28/0.54    inference(superposition,[],[f123,f55])).
% 1.28/0.54  fof(f123,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (k1_funct_1(sK6(X1,X2),sK4(sK6(X1,X2),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK6(X1,X2)))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f122,f52])).
% 1.28/0.54  fof(f122,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(sK6(X1,X2))) | k1_funct_1(sK6(X1,X2),sK4(sK6(X1,X2),X0)) = X0 | ~v1_relat_1(sK6(X1,X2))) )),
% 1.28/0.54    inference(resolution,[],[f58,f53])).
% 1.28/0.54  fof(f58,plain,(
% 1.28/0.54    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK4(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 1.28/0.54    inference(equality_resolution,[],[f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f51,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f32])).
% 1.28/0.54  fof(f155,plain,(
% 1.28/0.54    ~spl7_7),
% 1.28/0.54    inference(avatar_contradiction_clause,[],[f154])).
% 1.28/0.54  fof(f154,plain,(
% 1.28/0.54    $false | ~spl7_7),
% 1.28/0.54    inference(equality_resolution,[],[f138])).
% 1.28/0.54  fof(f138,plain,(
% 1.28/0.54    ( ! [X0] : (k1_xboole_0 != X0) ) | ~spl7_7),
% 1.28/0.54    inference(avatar_component_clause,[],[f137])).
% 1.28/0.54  fof(f137,plain,(
% 1.28/0.54    spl7_7 <=> ! [X0] : k1_xboole_0 != X0),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.28/0.54  fof(f142,plain,(
% 1.28/0.54    spl7_7 | spl7_8 | ~spl7_6),
% 1.28/0.54    inference(avatar_split_clause,[],[f135,f104,f140,f137])).
% 1.28/0.54  fof(f135,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (X1 = X2 | k1_xboole_0 != X0) ) | ~spl7_6),
% 1.28/0.54    inference(subsumption_resolution,[],[f134,f105])).
% 1.28/0.54  fof(f105,plain,(
% 1.28/0.54    ( ! [X1] : (r2_hidden(X1,k1_xboole_0)) ) | ~spl7_6),
% 1.28/0.54    inference(avatar_component_clause,[],[f104])).
% 1.28/0.54  fof(f134,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | X1 = X2 | k1_xboole_0 != X0) )),
% 1.28/0.54    inference(superposition,[],[f127,f76])).
% 1.28/0.54  fof(f113,plain,(
% 1.28/0.54    spl7_3 | ~spl7_5),
% 1.28/0.54    inference(avatar_contradiction_clause,[],[f110])).
% 1.28/0.54  fof(f110,plain,(
% 1.28/0.54    $false | (spl7_3 | ~spl7_5)),
% 1.28/0.54    inference(resolution,[],[f108,f84])).
% 1.28/0.54  fof(f108,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_5),
% 1.28/0.54    inference(resolution,[],[f107,f50])).
% 1.28/0.54  fof(f107,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_5),
% 1.28/0.54    inference(equality_resolution,[],[f102])).
% 1.28/0.54  fof(f102,plain,(
% 1.28/0.54    ( ! [X2,X0] : (k1_xboole_0 != X0 | ~r2_hidden(X2,X0)) ) | ~spl7_5),
% 1.28/0.54    inference(avatar_component_clause,[],[f101])).
% 1.28/0.54  fof(f70,plain,(
% 1.28/0.54    ~spl7_1 | spl7_2),
% 1.28/0.54    inference(avatar_split_clause,[],[f35,f67,f63])).
% 1.28/0.54  fof(f35,plain,(
% 1.28/0.54    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (16672)------------------------------
% 1.28/0.54  % (16672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (16672)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (16672)Memory used [KB]: 10874
% 1.28/0.54  % (16672)Time elapsed: 0.114 s
% 1.28/0.54  % (16672)------------------------------
% 1.28/0.54  % (16672)------------------------------
% 1.28/0.54  % (16669)Refutation not found, incomplete strategy% (16669)------------------------------
% 1.28/0.54  % (16669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (16669)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (16669)Memory used [KB]: 1663
% 1.28/0.54  % (16669)Time elapsed: 0.138 s
% 1.28/0.54  % (16669)------------------------------
% 1.28/0.54  % (16669)------------------------------
% 1.28/0.54  % (16689)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.54  % (16678)Refutation not found, incomplete strategy% (16678)------------------------------
% 1.28/0.54  % (16678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (16678)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (16678)Memory used [KB]: 10618
% 1.28/0.54  % (16678)Time elapsed: 0.136 s
% 1.28/0.54  % (16678)------------------------------
% 1.28/0.54  % (16678)------------------------------
% 1.28/0.54  % (16692)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.54  % (16668)Success in time 0.183 s
%------------------------------------------------------------------------------
