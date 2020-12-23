%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:50 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 321 expanded)
%              Number of leaves         :   16 ( 102 expanded)
%              Depth                    :   19
%              Number of atoms          :  434 (2250 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f99,f244,f288,f323])).

fof(f323,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f321,f92])).

fof(f92,plain,
    ( ~ r1_tarski(sK7,k1_relat_1(sK5))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl10_2
  <=> r1_tarski(sK7,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f321,plain,
    ( r1_tarski(sK7,k1_relat_1(sK5))
    | ~ spl10_1 ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,
    ( r1_tarski(sK7,k1_relat_1(sK5))
    | r1_tarski(sK7,k1_relat_1(sK5))
    | ~ spl10_1 ),
    inference(resolution,[],[f313,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

% (6873)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(X0,k1_relat_1(sK5)),sK7)
        | r1_tarski(X0,k1_relat_1(sK5)) )
    | ~ spl10_1 ),
    inference(resolution,[],[f312,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f312,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK5))
        | ~ r2_hidden(X0,sK7) )
    | ~ spl10_1 ),
    inference(resolution,[],[f311,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f311,plain,
    ( ! [X0] :
        ( sP3(sK6,X0,sK5)
        | ~ r2_hidden(X0,sK7) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f310,f56])).

fof(f56,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
      | ~ r1_tarski(sK7,k1_relat_1(sK5))
      | ~ r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) )
    & ( ( r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
        & r1_tarski(sK7,k1_relat_1(sK5)) )
      | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) )
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK5))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK5)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK5))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK5)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6))
            | ~ r1_tarski(X2,k1_relat_1(sK5))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6))) )
          & ( ( r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6))
              & r1_tarski(X2,k1_relat_1(sK5)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6))) ) )
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

% (6869)Refutation not found, incomplete strategy% (6869)------------------------------
% (6869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6869)Termination reason: Refutation not found, incomplete strategy

% (6869)Memory used [KB]: 10618
% (6869)Time elapsed: 0.173 s
% (6869)------------------------------
% (6869)------------------------------
% (6871)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (6861)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (6877)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (6881)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (6868)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (6878)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (6875)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (6862)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f35,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6))
          | ~ r1_tarski(X2,k1_relat_1(sK5))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6))) )
        & ( ( r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6))
            & r1_tarski(X2,k1_relat_1(sK5)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
        | ~ r1_tarski(sK7,k1_relat_1(sK5))
        | ~ r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) )
      & ( ( r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
          & r1_tarski(sK7,k1_relat_1(sK5)) )
        | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

% (6864)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f310,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7)
        | sP3(sK6,X0,sK5)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f309,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7)
        | sP3(sK6,X0,sK5)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f308,f54])).

fof(f54,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7)
        | sP3(sK6,X0,sK5)
        | ~ v1_relat_1(sK5)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f307,f55])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7)
        | sP3(sK6,X0,sK5)
        | ~ v1_funct_1(sK5)
        | ~ v1_relat_1(sK5)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_1 ),
    inference(resolution,[],[f297,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP4(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f18,f29,f28])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f297,plain,
    ( ! [X0] :
        ( ~ sP4(sK5,X0,sK6)
        | ~ r2_hidden(X0,sK7)
        | sP3(sK6,X0,sK5) )
    | ~ spl10_1 ),
    inference(resolution,[],[f155,f87])).

fof(f87,plain,
    ( r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_1
  <=> r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f155,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r1_tarski(X14,k1_relat_1(k5_relat_1(X13,X11)))
      | ~ sP4(X13,X12,X11)
      | ~ r2_hidden(X12,X14)
      | sP3(X11,X12,X13) ) ),
    inference(resolution,[],[f73,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2)))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f288,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl10_1
    | spl10_3 ),
    inference(subsumption_resolution,[],[f286,f54])).

fof(f286,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl10_1
    | spl10_3 ),
    inference(subsumption_resolution,[],[f285,f55])).

fof(f285,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl10_1
    | spl10_3 ),
    inference(subsumption_resolution,[],[f282,f255])).

fof(f255,plain,
    ( r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f254,f54])).

fof(f254,plain,
    ( r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | ~ v1_relat_1(sK5)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f253,f56])).

fof(f253,plain,
    ( r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ spl10_1 ),
    inference(superposition,[],[f87,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f282,plain,
    ( ~ r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl10_3 ),
    inference(resolution,[],[f281,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f281,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK5,X3),k1_relat_1(sK6))
        | ~ r1_tarski(sK7,X3) )
    | spl10_3 ),
    inference(subsumption_resolution,[],[f277,f54])).

fof(f277,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK5,X3),k1_relat_1(sK6))
        | ~ r1_tarski(sK7,X3)
        | ~ v1_relat_1(sK5) )
    | spl10_3 ),
    inference(resolution,[],[f256,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK5,sK7),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK6)) )
    | spl10_3 ),
    inference(resolution,[],[f96,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f112,f80])).

fof(f112,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK9(X4,X3),X5)
      | r1_tarski(X4,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X5,X2) ) ),
    inference(resolution,[],[f102,f79])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X2)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f79,f81])).

% (6863)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (6876)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f96,plain,
    ( ~ r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl10_3
  <=> r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f244,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f242,f54])).

fof(f242,plain,
    ( ~ v1_relat_1(sK5)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f241,f55])).

fof(f241,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f240,f91])).

fof(f91,plain,
    ( r1_tarski(sK7,k1_relat_1(sK5))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f240,plain,
    ( ~ r1_tarski(sK7,k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl10_1
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f235,f95])).

fof(f95,plain,
    ( r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f235,plain,
    ( ~ r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
    | ~ r1_tarski(sK7,k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl10_1 ),
    inference(resolution,[],[f83,f128])).

fof(f128,plain,
    ( ~ r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f127,plain,
    ( ~ r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | ~ v1_relat_1(sK5)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f125,f56])).

fof(f125,plain,
    ( ~ r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6)))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | spl10_1 ),
    inference(superposition,[],[f88,f61])).

fof(f88,plain,
    ( ~ r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f99,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f58,f90,f86])).

fof(f58,plain,
    ( r1_tarski(sK7,k1_relat_1(sK5))
    | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f59,f94,f86])).

fof(f59,plain,
    ( r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
    | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f60,f94,f90,f86])).

fof(f60,plain,
    ( ~ r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))
    | ~ r1_tarski(sK7,k1_relat_1(sK5))
    | ~ r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (6858)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.55  % (6866)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.55  % (6867)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.56  % (6874)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.56  % (6859)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.56  % (6857)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.58/0.57  % (6856)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.58/0.57  % (6860)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.58/0.57  % (6879)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.58  % (6874)Refutation not found, incomplete strategy% (6874)------------------------------
% 1.58/0.58  % (6874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (6874)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (6874)Memory used [KB]: 10746
% 1.58/0.58  % (6874)Time elapsed: 0.140 s
% 1.58/0.58  % (6874)------------------------------
% 1.58/0.58  % (6874)------------------------------
% 1.58/0.58  % (6854)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.59  % (6855)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.59  % (6880)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.59  % (6865)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.59  % (6852)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.58/0.60  % (6870)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.60  % (6869)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.60  % (6853)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.60  % (6879)Refutation found. Thanks to Tanya!
% 1.58/0.60  % SZS status Theorem for theBenchmark
% 1.58/0.60  % SZS output start Proof for theBenchmark
% 1.58/0.60  fof(f324,plain,(
% 1.58/0.60    $false),
% 1.58/0.60    inference(avatar_sat_refutation,[],[f97,f98,f99,f244,f288,f323])).
% 1.58/0.60  fof(f323,plain,(
% 1.58/0.60    ~spl10_1 | spl10_2),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f322])).
% 1.58/0.60  fof(f322,plain,(
% 1.58/0.60    $false | (~spl10_1 | spl10_2)),
% 1.58/0.60    inference(subsumption_resolution,[],[f321,f92])).
% 1.58/0.60  fof(f92,plain,(
% 1.58/0.60    ~r1_tarski(sK7,k1_relat_1(sK5)) | spl10_2),
% 1.58/0.60    inference(avatar_component_clause,[],[f90])).
% 1.58/0.60  fof(f90,plain,(
% 1.58/0.60    spl10_2 <=> r1_tarski(sK7,k1_relat_1(sK5))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.58/0.60  fof(f321,plain,(
% 1.58/0.60    r1_tarski(sK7,k1_relat_1(sK5)) | ~spl10_1),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f319])).
% 1.58/0.60  fof(f319,plain,(
% 1.58/0.60    r1_tarski(sK7,k1_relat_1(sK5)) | r1_tarski(sK7,k1_relat_1(sK5)) | ~spl10_1),
% 1.58/0.60    inference(resolution,[],[f313,f80])).
% 1.58/0.60  fof(f80,plain,(
% 1.58/0.60    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f53])).
% 1.58/0.60  fof(f53,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f51,f52])).
% 1.58/0.60  fof(f52,plain,(
% 1.58/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f51,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(rectify,[],[f50])).
% 1.58/0.60  % (6873)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.60  fof(f50,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(nnf_transformation,[],[f19])).
% 1.58/0.60  fof(f19,plain,(
% 1.58/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.60    inference(ennf_transformation,[],[f1])).
% 1.58/0.60  fof(f1,axiom,(
% 1.58/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.60  fof(f313,plain,(
% 1.58/0.60    ( ! [X0] : (~r2_hidden(sK9(X0,k1_relat_1(sK5)),sK7) | r1_tarski(X0,k1_relat_1(sK5))) ) | ~spl10_1),
% 1.58/0.60    inference(resolution,[],[f312,f81])).
% 1.58/0.60  fof(f81,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f53])).
% 1.58/0.60  fof(f312,plain,(
% 1.58/0.60    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK5)) | ~r2_hidden(X0,sK7)) ) | ~spl10_1),
% 1.58/0.60    inference(resolution,[],[f311,f75])).
% 1.58/0.60  fof(f75,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r2_hidden(X1,k1_relat_1(X2))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f49])).
% 1.58/0.60  fof(f49,plain,(
% 1.58/0.60    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X2))) | ~sP3(X0,X1,X2)))),
% 1.58/0.60    inference(rectify,[],[f48])).
% 1.58/0.60  fof(f48,plain,(
% 1.58/0.60    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~sP3(X1,X0,X2)))),
% 1.58/0.60    inference(flattening,[],[f47])).
% 1.58/0.60  fof(f47,plain,(
% 1.58/0.60    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~sP3(X1,X0,X2)))),
% 1.58/0.60    inference(nnf_transformation,[],[f28])).
% 1.58/0.60  fof(f28,plain,(
% 1.58/0.60    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))),
% 1.58/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.58/0.60  fof(f311,plain,(
% 1.58/0.60    ( ! [X0] : (sP3(sK6,X0,sK5) | ~r2_hidden(X0,sK7)) ) | ~spl10_1),
% 1.58/0.60    inference(subsumption_resolution,[],[f310,f56])).
% 1.58/0.60  fof(f56,plain,(
% 1.58/0.60    v1_relat_1(sK6)),
% 1.58/0.60    inference(cnf_transformation,[],[f36])).
% 1.58/0.60  fof(f36,plain,(
% 1.58/0.60    (((~r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | ~r1_tarski(sK7,k1_relat_1(sK5)) | ~r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))) & ((r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) & r1_tarski(sK7,k1_relat_1(sK5))) | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))))) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f35,f34,f33])).
% 1.58/0.60  fof(f33,plain,(
% 1.58/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK5)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1)))) & ((r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK5))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f34,plain,(
% 1.58/0.60    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK5)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1)))) & ((r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK5))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6)) | ~r1_tarski(X2,k1_relat_1(sK5)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6)))) & ((r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6)) & r1_tarski(X2,k1_relat_1(sK5))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6))))) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  % (6869)Refutation not found, incomplete strategy% (6869)------------------------------
% 1.58/0.60  % (6869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (6869)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (6869)Memory used [KB]: 10618
% 1.58/0.60  % (6869)Time elapsed: 0.173 s
% 1.58/0.60  % (6869)------------------------------
% 1.58/0.60  % (6869)------------------------------
% 1.58/0.61  % (6871)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.58/0.61  % (6861)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.61  % (6877)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.61  % (6881)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.58/0.62  % (6868)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.62  % (6878)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.62  % (6875)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.62  % (6862)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.62  fof(f35,plain,(
% 1.58/0.62    ? [X2] : ((~r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6)) | ~r1_tarski(X2,k1_relat_1(sK5)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6)))) & ((r1_tarski(k9_relat_1(sK5,X2),k1_relat_1(sK6)) & r1_tarski(X2,k1_relat_1(sK5))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK5,sK6))))) => ((~r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | ~r1_tarski(sK7,k1_relat_1(sK5)) | ~r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))) & ((r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) & r1_tarski(sK7,k1_relat_1(sK5))) | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))))),
% 1.58/0.62    introduced(choice_axiom,[])).
% 1.58/0.62  fof(f32,plain,(
% 1.58/0.62    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.58/0.62    inference(flattening,[],[f31])).
% 1.58/0.62  fof(f31,plain,(
% 1.58/0.62    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.58/0.62    inference(nnf_transformation,[],[f11])).
% 1.58/0.62  fof(f11,plain,(
% 1.58/0.62    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.58/0.62    inference(flattening,[],[f10])).
% 1.58/0.62  fof(f10,plain,(
% 1.58/0.62    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.58/0.62    inference(ennf_transformation,[],[f9])).
% 1.58/0.62  fof(f9,negated_conjecture,(
% 1.58/0.62    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.58/0.62    inference(negated_conjecture,[],[f8])).
% 1.58/0.63  % (6864)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.63  fof(f8,conjecture,(
% 1.58/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 1.58/0.63  fof(f310,plain,(
% 1.58/0.63    ( ! [X0] : (~r2_hidden(X0,sK7) | sP3(sK6,X0,sK5) | ~v1_relat_1(sK6)) ) | ~spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f309,f57])).
% 1.58/0.63  fof(f57,plain,(
% 1.58/0.63    v1_funct_1(sK6)),
% 1.58/0.63    inference(cnf_transformation,[],[f36])).
% 1.58/0.63  fof(f309,plain,(
% 1.58/0.63    ( ! [X0] : (~r2_hidden(X0,sK7) | sP3(sK6,X0,sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f308,f54])).
% 1.58/0.63  fof(f54,plain,(
% 1.58/0.63    v1_relat_1(sK5)),
% 1.58/0.63    inference(cnf_transformation,[],[f36])).
% 1.58/0.63  fof(f308,plain,(
% 1.58/0.63    ( ! [X0] : (~r2_hidden(X0,sK7) | sP3(sK6,X0,sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f307,f55])).
% 1.58/0.63  fof(f55,plain,(
% 1.58/0.63    v1_funct_1(sK5)),
% 1.58/0.63    inference(cnf_transformation,[],[f36])).
% 1.58/0.63  fof(f307,plain,(
% 1.58/0.63    ( ! [X0] : (~r2_hidden(X0,sK7) | sP3(sK6,X0,sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl10_1),
% 1.58/0.63    inference(resolution,[],[f297,f78])).
% 1.58/0.63  fof(f78,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f30])).
% 1.58/0.63  fof(f30,plain,(
% 1.58/0.63    ! [X0,X1] : (! [X2] : (sP4(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.63    inference(definition_folding,[],[f18,f29,f28])).
% 1.58/0.63  fof(f29,plain,(
% 1.58/0.63    ! [X2,X0,X1] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 1.58/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.58/0.63  fof(f18,plain,(
% 1.58/0.63    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.63    inference(flattening,[],[f17])).
% 1.58/0.63  fof(f17,plain,(
% 1.58/0.63    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.63    inference(ennf_transformation,[],[f7])).
% 1.58/0.63  fof(f7,axiom,(
% 1.58/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 1.58/0.63  fof(f297,plain,(
% 1.58/0.63    ( ! [X0] : (~sP4(sK5,X0,sK6) | ~r2_hidden(X0,sK7) | sP3(sK6,X0,sK5)) ) | ~spl10_1),
% 1.58/0.63    inference(resolution,[],[f155,f87])).
% 1.58/0.63  fof(f87,plain,(
% 1.58/0.63    r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) | ~spl10_1),
% 1.58/0.63    inference(avatar_component_clause,[],[f86])).
% 1.58/0.63  fof(f86,plain,(
% 1.58/0.63    spl10_1 <=> r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))),
% 1.58/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.58/0.63  fof(f155,plain,(
% 1.58/0.63    ( ! [X14,X12,X13,X11] : (~r1_tarski(X14,k1_relat_1(k5_relat_1(X13,X11))) | ~sP4(X13,X12,X11) | ~r2_hidden(X12,X14) | sP3(X11,X12,X13)) )),
% 1.58/0.63    inference(resolution,[],[f73,f79])).
% 1.58/0.63  fof(f79,plain,(
% 1.58/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f53])).
% 1.58/0.63  fof(f73,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f46])).
% 1.58/0.63  fof(f46,plain,(
% 1.58/0.63    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,X2))))) | ~sP4(X0,X1,X2))),
% 1.58/0.63    inference(rectify,[],[f45])).
% 1.58/0.63  fof(f45,plain,(
% 1.58/0.63    ! [X2,X0,X1] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~sP4(X2,X0,X1))),
% 1.58/0.63    inference(nnf_transformation,[],[f29])).
% 1.58/0.63  fof(f288,plain,(
% 1.58/0.63    ~spl10_1 | spl10_3),
% 1.58/0.63    inference(avatar_contradiction_clause,[],[f287])).
% 1.58/0.63  fof(f287,plain,(
% 1.58/0.63    $false | (~spl10_1 | spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f286,f54])).
% 1.58/0.63  fof(f286,plain,(
% 1.58/0.63    ~v1_relat_1(sK5) | (~spl10_1 | spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f285,f55])).
% 1.58/0.63  fof(f285,plain,(
% 1.58/0.63    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | (~spl10_1 | spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f282,f255])).
% 1.58/0.63  fof(f255,plain,(
% 1.58/0.63    r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | ~spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f254,f54])).
% 1.58/0.63  fof(f254,plain,(
% 1.58/0.63    r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | ~v1_relat_1(sK5) | ~spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f253,f56])).
% 1.58/0.63  fof(f253,plain,(
% 1.58/0.63    r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | ~v1_relat_1(sK6) | ~v1_relat_1(sK5) | ~spl10_1),
% 1.58/0.63    inference(superposition,[],[f87,f61])).
% 1.58/0.63  fof(f61,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f12])).
% 1.58/0.63  fof(f12,plain,(
% 1.58/0.63    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.58/0.63    inference(ennf_transformation,[],[f3])).
% 1.58/0.63  fof(f3,axiom,(
% 1.58/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.58/0.63  fof(f282,plain,(
% 1.58/0.63    ~r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl10_3),
% 1.58/0.63    inference(resolution,[],[f281,f72])).
% 1.58/0.63  fof(f72,plain,(
% 1.58/0.63    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f16])).
% 1.58/0.63  fof(f16,plain,(
% 1.58/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.63    inference(flattening,[],[f15])).
% 1.58/0.63  fof(f15,plain,(
% 1.58/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.63    inference(ennf_transformation,[],[f5])).
% 1.58/0.63  fof(f5,axiom,(
% 1.58/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.58/0.63  fof(f281,plain,(
% 1.58/0.63    ( ! [X3] : (~r1_tarski(k9_relat_1(sK5,X3),k1_relat_1(sK6)) | ~r1_tarski(sK7,X3)) ) | spl10_3),
% 1.58/0.63    inference(subsumption_resolution,[],[f277,f54])).
% 1.58/0.63  fof(f277,plain,(
% 1.58/0.63    ( ! [X3] : (~r1_tarski(k9_relat_1(sK5,X3),k1_relat_1(sK6)) | ~r1_tarski(sK7,X3) | ~v1_relat_1(sK5)) ) | spl10_3),
% 1.58/0.63    inference(resolution,[],[f256,f82])).
% 1.58/0.63  fof(f82,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f21])).
% 1.58/0.63  fof(f21,plain,(
% 1.58/0.63    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.58/0.63    inference(flattening,[],[f20])).
% 1.58/0.63  fof(f20,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.58/0.63    inference(ennf_transformation,[],[f2])).
% 1.58/0.63  fof(f2,axiom,(
% 1.58/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.58/0.63  fof(f256,plain,(
% 1.58/0.63    ( ! [X0] : (~r1_tarski(k9_relat_1(sK5,sK7),X0) | ~r1_tarski(X0,k1_relat_1(sK6))) ) | spl10_3),
% 1.58/0.63    inference(resolution,[],[f96,f175])).
% 1.58/0.63  fof(f175,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2)) )),
% 1.58/0.63    inference(duplicate_literal_removal,[],[f171])).
% 1.58/0.63  fof(f171,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.58/0.63    inference(resolution,[],[f112,f80])).
% 1.58/0.63  fof(f112,plain,(
% 1.58/0.63    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK9(X4,X3),X5) | r1_tarski(X4,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X5,X2)) )),
% 1.58/0.63    inference(resolution,[],[f102,f79])).
% 1.58/0.63  fof(f102,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK9(X0,X1),X2) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 1.58/0.63    inference(resolution,[],[f79,f81])).
% 1.58/0.63  % (6863)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.63  % (6876)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.63  fof(f96,plain,(
% 1.58/0.63    ~r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | spl10_3),
% 1.58/0.63    inference(avatar_component_clause,[],[f94])).
% 1.58/0.63  fof(f94,plain,(
% 1.58/0.63    spl10_3 <=> r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6))),
% 1.58/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.58/0.63  fof(f244,plain,(
% 1.58/0.63    spl10_1 | ~spl10_2 | ~spl10_3),
% 1.58/0.63    inference(avatar_contradiction_clause,[],[f243])).
% 1.58/0.63  fof(f243,plain,(
% 1.58/0.63    $false | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f242,f54])).
% 1.58/0.63  fof(f242,plain,(
% 1.58/0.63    ~v1_relat_1(sK5) | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f241,f55])).
% 1.58/0.63  fof(f241,plain,(
% 1.58/0.63    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f240,f91])).
% 1.58/0.63  fof(f91,plain,(
% 1.58/0.63    r1_tarski(sK7,k1_relat_1(sK5)) | ~spl10_2),
% 1.58/0.63    inference(avatar_component_clause,[],[f90])).
% 1.58/0.63  fof(f240,plain,(
% 1.58/0.63    ~r1_tarski(sK7,k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | (spl10_1 | ~spl10_3)),
% 1.58/0.63    inference(subsumption_resolution,[],[f235,f95])).
% 1.58/0.63  fof(f95,plain,(
% 1.58/0.63    r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | ~spl10_3),
% 1.58/0.63    inference(avatar_component_clause,[],[f94])).
% 1.58/0.63  fof(f235,plain,(
% 1.58/0.63    ~r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | ~r1_tarski(sK7,k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl10_1),
% 1.58/0.63    inference(resolution,[],[f83,f128])).
% 1.58/0.63  fof(f128,plain,(
% 1.58/0.63    ~r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f127,f54])).
% 1.58/0.63  fof(f127,plain,(
% 1.58/0.63    ~r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | ~v1_relat_1(sK5) | spl10_1),
% 1.58/0.63    inference(subsumption_resolution,[],[f125,f56])).
% 1.58/0.63  fof(f125,plain,(
% 1.58/0.63    ~r1_tarski(sK7,k10_relat_1(sK5,k1_relat_1(sK6))) | ~v1_relat_1(sK6) | ~v1_relat_1(sK5) | spl10_1),
% 1.58/0.63    inference(superposition,[],[f88,f61])).
% 1.58/0.63  fof(f88,plain,(
% 1.58/0.63    ~r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6))) | spl10_1),
% 1.58/0.63    inference(avatar_component_clause,[],[f86])).
% 1.58/0.63  fof(f83,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f23])).
% 1.58/0.63  fof(f23,plain,(
% 1.58/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.58/0.63    inference(flattening,[],[f22])).
% 1.58/0.63  fof(f22,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.58/0.63    inference(ennf_transformation,[],[f6])).
% 1.58/0.63  fof(f6,axiom,(
% 1.58/0.63    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.58/0.63  fof(f99,plain,(
% 1.58/0.63    spl10_1 | spl10_2),
% 1.58/0.63    inference(avatar_split_clause,[],[f58,f90,f86])).
% 1.58/0.63  fof(f58,plain,(
% 1.58/0.63    r1_tarski(sK7,k1_relat_1(sK5)) | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))),
% 1.58/0.63    inference(cnf_transformation,[],[f36])).
% 1.58/0.63  fof(f98,plain,(
% 1.58/0.63    spl10_1 | spl10_3),
% 1.58/0.63    inference(avatar_split_clause,[],[f59,f94,f86])).
% 1.58/0.63  fof(f59,plain,(
% 1.58/0.63    r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))),
% 1.58/0.63    inference(cnf_transformation,[],[f36])).
% 1.58/0.63  fof(f97,plain,(
% 1.58/0.63    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 1.58/0.63    inference(avatar_split_clause,[],[f60,f94,f90,f86])).
% 1.58/0.63  fof(f60,plain,(
% 1.58/0.63    ~r1_tarski(k9_relat_1(sK5,sK7),k1_relat_1(sK6)) | ~r1_tarski(sK7,k1_relat_1(sK5)) | ~r1_tarski(sK7,k1_relat_1(k5_relat_1(sK5,sK6)))),
% 1.58/0.63    inference(cnf_transformation,[],[f36])).
% 1.58/0.63  % SZS output end Proof for theBenchmark
% 1.58/0.64  % (6872)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.58/0.64  % (6879)------------------------------
% 1.58/0.64  % (6879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.64  % (6879)Termination reason: Refutation
% 1.58/0.64  
% 1.58/0.64  % (6879)Memory used [KB]: 6396
% 1.58/0.64  % (6879)Time elapsed: 0.174 s
% 1.58/0.64  % (6879)------------------------------
% 1.58/0.64  % (6879)------------------------------
% 1.58/0.64  % (6851)Success in time 0.281 s
%------------------------------------------------------------------------------
