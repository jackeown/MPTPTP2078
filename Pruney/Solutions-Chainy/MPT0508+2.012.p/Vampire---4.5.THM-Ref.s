%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 156 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 657 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f90,f100,f128,f131,f139])).

fof(f139,plain,
    ( ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(resolution,[],[f127,f105])).

fof(f105,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK1),k7_relat_1(sK3,sK1))
    | ~ spl5_8 ),
    inference(resolution,[],[f101,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f41])).

% (1863)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK1),X0)
        | ~ r1_tarski(X0,k7_relat_1(sK3,sK1)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f99,f31])).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X1,k7_relat_1(sK3,sK1)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X1,k7_relat_1(sK3,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f127,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_11
  <=> ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f131,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f124,f30])).

fof(f30,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f124,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_10
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f128,plain,
    ( ~ spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f118,f126,f122])).

fof(f118,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))
      | ~ r1_tarski(sK2,sK3) ) ),
    inference(resolution,[],[f113,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(sK3,X3))
      | ~ r1_tarski(X2,sK3) ) ),
    inference(resolution,[],[f34,f29])).

fof(f29,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

% (1858)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f100,plain,
    ( ~ spl5_4
    | spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f94,f64,f98,f74])).

fof(f74,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f64,plain,
    ( spl5_3
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(X1,k7_relat_1(sK3,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X1,k7_relat_1(sK3,sK1))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,k7_relat_1(sK3,sK1)) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f76,f28])).

fof(f76,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f70,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f61,f64,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,k7_relat_1(sK3,sK1))
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
      | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X3)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X1,k7_relat_1(sK3,sK1))
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X1)
      | ~ r1_tarski(X0,k7_relat_1(sK3,sK1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f44,f35])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0)
      | ~ r1_tarski(X0,k7_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK4(X0,X1),X2) ) ),
    inference(resolution,[],[f35,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (1868)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (1860)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1867)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1861)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1856)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (1866)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1855)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (1857)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1883)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1880)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1881)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (1875)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (1872)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (1873)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (1882)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (1872)Refutation not found, incomplete strategy% (1872)------------------------------
% 0.21/0.55  % (1872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1872)Memory used [KB]: 10618
% 0.21/0.55  % (1872)Time elapsed: 0.117 s
% 0.21/0.55  % (1872)------------------------------
% 0.21/0.55  % (1872)------------------------------
% 0.21/0.55  % (1859)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (1867)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f66,f70,f90,f100,f128,f131,f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ~spl5_8 | ~spl5_11),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    $false | (~spl5_8 | ~spl5_11)),
% 0.21/0.55    inference(resolution,[],[f127,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ~r1_tarski(k7_relat_1(sK2,sK1),k7_relat_1(sK3,sK1)) | ~spl5_8),
% 0.21/0.55    inference(resolution,[],[f101,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f41])).
% 0.21/0.55  % (1863)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f37,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k7_relat_1(sK2,sK1),X0) | ~r1_tarski(X0,k7_relat_1(sK3,sK1))) ) | ~spl5_8),
% 0.21/0.55    inference(resolution,[],[f99,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~r1_tarski(X1,k7_relat_1(sK3,sK1))) ) | ~spl5_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl5_8 <=> ! [X1,X0] : (~r1_tarski(k7_relat_1(sK2,X0),X1) | ~r1_tarski(sK0,X0) | ~r1_tarski(X1,k7_relat_1(sK3,sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))) ) | ~spl5_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl5_11 <=> ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    spl5_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    $false | spl5_10),
% 0.21/0.55    inference(resolution,[],[f124,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    r1_tarski(sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ~r1_tarski(sK2,sK3) | spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    spl5_10 <=> r1_tarski(sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    ~spl5_10 | spl5_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f118,f126,f122])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0)) | ~r1_tarski(sK2,sK3)) )),
% 0.21/0.55    inference(resolution,[],[f113,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    v1_relat_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~v1_relat_1(X2) | r1_tarski(k7_relat_1(X2,X3),k7_relat_1(sK3,X3)) | ~r1_tarski(X2,sK3)) )),
% 0.21/0.55    inference(resolution,[],[f34,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    v1_relat_1(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X1,X2) | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  % (1858)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ~spl5_4 | spl5_8 | ~spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f94,f64,f98,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    spl5_4 <=> v1_relat_1(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl5_3 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~r1_tarski(k7_relat_1(sK2,sK0),X0) | ~r1_tarski(X1,k7_relat_1(sK3,sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK2,X0),X1) | ~r1_tarski(X1,k7_relat_1(sK3,sK1)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK2)) ) | ~spl5_3),
% 0.21/0.55    inference(resolution,[],[f65,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK2,sK0),X0) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,k7_relat_1(sK3,sK1))) ) | ~spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f64])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl5_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    $false | spl5_4),
% 0.21/0.55    inference(resolution,[],[f76,f28])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ~v1_relat_1(sK2) | spl5_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f74])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ~spl5_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    $false | ~spl5_1),
% 0.21/0.55    inference(resolution,[],[f52,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | ~spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    spl5_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    spl5_1 | spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f61,f64,f50])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,k7_relat_1(sK3,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X0) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f48,f36])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X2,X3,X1] : (~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X3) | ~r1_tarski(X2,X1) | ~r1_tarski(X1,k7_relat_1(sK3,sK1)) | ~r1_tarski(X3,X2)) )),
% 0.21/0.55    inference(resolution,[],[f46,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X1) | ~r1_tarski(X0,k7_relat_1(sK3,sK1)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.55    inference(resolution,[],[f44,f35])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0) | ~r1_tarski(X0,k7_relat_1(sK3,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f43,f32])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK4(X0,X1),X2)) )),
% 0.21/0.55    inference(resolution,[],[f35,f37])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (1867)------------------------------
% 0.21/0.55  % (1867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1867)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (1867)Memory used [KB]: 6268
% 0.21/0.55  % (1867)Time elapsed: 0.109 s
% 0.21/0.55  % (1867)------------------------------
% 0.21/0.55  % (1867)------------------------------
% 0.21/0.55  % (1854)Success in time 0.189 s
%------------------------------------------------------------------------------
