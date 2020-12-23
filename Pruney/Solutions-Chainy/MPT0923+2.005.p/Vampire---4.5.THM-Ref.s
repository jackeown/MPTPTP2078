%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 146 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   23
%              Number of atoms          :  202 ( 469 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f61,f63,f65,f67])).

fof(f67,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f16,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK0
        | ~ r2_hidden(X8,sK4)
        | ~ r2_hidden(X7,sK3)
        | ~ r2_hidden(X6,sK2)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK0
          | ~ r2_hidden(X8,sK4)
          | ~ r2_hidden(X7,sK3)
          | ~ r2_hidden(X6,sK2)
          | ~ r2_hidden(X5,sK1) )
      & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f49,plain,
    ( ! [X6,X8,X7] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK2),X7),X8))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_1
  <=> ! [X7,X8,X6] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK2),X7),X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f65,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl5_4 ),
    inference(resolution,[],[f58,f29])).

fof(f58,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,sK4))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_4
  <=> ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f63,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f29])).

fof(f55,plain,
    ( ! [X2,X1] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> ! [X1,X2] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f61,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl5_2 ),
    inference(resolution,[],[f52,f29])).

fof(f52,plain,
    ( ! [X4,X5,X3] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4),X5))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_2
  <=> ! [X3,X5,X4] : ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4),X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f59,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f46,f57,f54,f51,f48])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,sK4))
      | ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2))
      | ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4),X5))
      | ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK2),X7),X8)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK4))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK3),X3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X4),X5),X6))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,sK2),X8),X9)) ) ),
    inference(resolution,[],[f44,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X1,sK2),X2))
      | sK0 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK4))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK3),X5))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X6),X7),X8)) ) ),
    inference(resolution,[],[f43,f22])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X1),X2))
      | sK0 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X3,sK2),X4))
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK4))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X6,sK3),X7)) ) ),
    inference(resolution,[],[f42,f22])).

fof(f42,plain,(
    ! [X4,X2,X0,X8,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK3))
      | sK0 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X2),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X4,sK2),X5))
      | ~ r2_hidden(X0,k2_zfmisc_1(X8,sK4)) ) ),
    inference(condensation,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sK0 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X2),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X4,sK2),X5))
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,X7))
      | ~ r2_hidden(X0,k2_zfmisc_1(X8,sK4)) ) ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK4)
      | sK0 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X2),X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X4,sK2),X5))
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,X7)) ) ),
    inference(superposition,[],[f39,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,sK3))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X5,sK2),X6)) ) ),
    inference(resolution,[],[f38,f22])).

% (8574)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(X0,sK4)
      | sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X1,k2_zfmisc_1(X3,sK3))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,X4),X5)) ) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK1,X3))
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK2))
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK3)) ) ),
    inference(condensation,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK1,X3))
      | ~ r2_hidden(X0,k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK3)) ) ),
    inference(resolution,[],[f35,f23])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK3)
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK1,X3))
      | ~ r2_hidden(X0,k2_zfmisc_1(X4,X5)) ) ),
    inference(superposition,[],[f34,f30])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK0 != k4_tarski(k4_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X2,sK4)
      | ~ r2_hidden(X1,k2_zfmisc_1(X3,sK2))
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,X4)) ) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k1_mcart_1(X2),sK1)
      | ~ r2_hidden(X1,sK3)
      | sK0 != k4_tarski(k4_tarski(X2,X1),X0)
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X2,k2_zfmisc_1(X5,sK2)) ) ),
    inference(condensation,[],[f32])).

% (8559)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X1,sK3)
      | sK0 != k4_tarski(k4_tarski(X2,X1),X0)
      | ~ r2_hidden(k1_mcart_1(X2),sK1)
      | ~ r2_hidden(X2,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(X2,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(X2,sK4)
      | ~ r2_hidden(X1,sK3)
      | k4_tarski(k4_tarski(X0,X1),X2) != sK0
      | ~ r2_hidden(k1_mcart_1(X0),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f28,f30])).

fof(f28,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f17,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f17,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK0
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (8569)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (8563)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (8569)Refutation not found, incomplete strategy% (8569)------------------------------
% 0.20/0.50  % (8569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8569)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8569)Memory used [KB]: 10618
% 0.20/0.50  % (8569)Time elapsed: 0.094 s
% 0.20/0.50  % (8569)------------------------------
% 0.20/0.50  % (8569)------------------------------
% 0.20/0.50  % (8567)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (8567)Refutation not found, incomplete strategy% (8567)------------------------------
% 0.20/0.50  % (8567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8567)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8567)Memory used [KB]: 10618
% 0.20/0.50  % (8567)Time elapsed: 0.091 s
% 0.20/0.50  % (8567)------------------------------
% 0.20/0.50  % (8567)------------------------------
% 0.20/0.50  % (8561)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (8564)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (8561)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f59,f61,f63,f65,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ~spl5_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    $false | ~spl5_1),
% 0.20/0.51    inference(resolution,[],[f49,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.20/0.51    inference(definition_unfolding,[],[f16,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f25,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4))) => (! [X8,X7,X6,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) & r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK2),X7),X8))) ) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    spl5_1 <=> ! [X7,X8,X6] : ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK2),X7),X8))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~spl5_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    $false | ~spl5_4),
% 0.20/0.51    inference(resolution,[],[f58,f29])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(X0,sK4))) ) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl5_4 <=> ! [X0] : ~r2_hidden(sK0,k2_zfmisc_1(X0,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~spl5_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    $false | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f55,f29])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2))) ) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl5_3 <=> ! [X1,X2] : ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~spl5_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    $false | ~spl5_2),
% 0.20/0.51    inference(resolution,[],[f52,f29])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X4,X5,X3] : (~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4),X5))) ) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl5_2 <=> ! [X3,X5,X4] : ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4),X5))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl5_1 | spl5_2 | spl5_3 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f57,f54,f51,f48])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,sK4)) | ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2)) | ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4),X5)) | ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,sK2),X7),X8))) )),
% 0.20/0.51    inference(equality_resolution,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sK0 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,sK4)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK3),X3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X4),X5),X6)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,sK2),X8),X9))) )),
% 0.20/0.51    inference(resolution,[],[f44,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X1,sK2),X2)) | sK0 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X3,sK4)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X4,sK3),X5)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,X6),X7),X8))) )),
% 0.20/0.51    inference(resolution,[],[f43,f22])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X1),X2)) | sK0 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X3,sK2),X4)) | ~r2_hidden(X0,k2_zfmisc_1(X5,sK4)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X6,sK3),X7))) )),
% 0.20/0.51    inference(resolution,[],[f42,f22])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X8,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK3)) | sK0 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X2),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X4,sK2),X5)) | ~r2_hidden(X0,k2_zfmisc_1(X8,sK4))) )),
% 0.20/0.51    inference(condensation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sK0 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X2),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X4,sK2),X5)) | ~r2_hidden(X0,k2_zfmisc_1(X6,X7)) | ~r2_hidden(X0,k2_zfmisc_1(X8,sK4))) )),
% 0.20/0.51    inference(resolution,[],[f40,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK4) | sK0 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(sK1,X2),X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(k2_zfmisc_1(X4,sK2),X5)) | ~r2_hidden(X0,k2_zfmisc_1(X6,X7))) )),
% 0.20/0.51    inference(superposition,[],[f39,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(resolution,[],[f19,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sK0 != k4_tarski(X1,X0) | ~r2_hidden(X0,sK4) | ~r2_hidden(X1,k2_zfmisc_1(X2,sK3)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,X3),X4)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X5,sK2),X6))) )),
% 0.20/0.51    inference(resolution,[],[f38,f22])).
% 0.20/0.51  % (8574)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK2)) | ~r2_hidden(X0,sK4) | sK0 != k4_tarski(X1,X0) | ~r2_hidden(X1,k2_zfmisc_1(X3,sK3)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,X4),X5))) )),
% 0.20/0.51    inference(resolution,[],[f37,f22])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X6,X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK1,X3)) | ~r2_hidden(X1,sK4) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK2)) | k4_tarski(X0,X1) != sK0 | ~r2_hidden(X0,k2_zfmisc_1(X6,sK3))) )),
% 0.20/0.51    inference(condensation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k4_tarski(X0,X1) != sK0 | ~r2_hidden(X1,sK4) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK1,X3)) | ~r2_hidden(X0,k2_zfmisc_1(X4,X5)) | ~r2_hidden(X0,k2_zfmisc_1(X6,sK3))) )),
% 0.20/0.51    inference(resolution,[],[f35,f23])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK3) | k4_tarski(X0,X1) != sK0 | ~r2_hidden(X1,sK4) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK1,X3)) | ~r2_hidden(X0,k2_zfmisc_1(X4,X5))) )),
% 0.20/0.51    inference(superposition,[],[f34,f30])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (sK0 != k4_tarski(k4_tarski(X1,X0),X2) | ~r2_hidden(X0,sK3) | ~r2_hidden(X2,sK4) | ~r2_hidden(X1,k2_zfmisc_1(X3,sK2)) | ~r2_hidden(X1,k2_zfmisc_1(sK1,X4))) )),
% 0.20/0.51    inference(resolution,[],[f33,f22])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X1] : (~r2_hidden(k1_mcart_1(X2),sK1) | ~r2_hidden(X1,sK3) | sK0 != k4_tarski(k4_tarski(X2,X1),X0) | ~r2_hidden(X0,sK4) | ~r2_hidden(X2,k2_zfmisc_1(X5,sK2))) )),
% 0.20/0.51    inference(condensation,[],[f32])).
% 0.20/0.51  % (8559)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X0,sK4) | ~r2_hidden(X1,sK3) | sK0 != k4_tarski(k4_tarski(X2,X1),X0) | ~r2_hidden(k1_mcart_1(X2),sK1) | ~r2_hidden(X2,k2_zfmisc_1(X3,X4)) | ~r2_hidden(X2,k2_zfmisc_1(X5,sK2))) )),
% 0.20/0.51    inference(resolution,[],[f31,f23])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~r2_hidden(X2,sK4) | ~r2_hidden(X1,sK3) | k4_tarski(k4_tarski(X0,X1),X2) != sK0 | ~r2_hidden(k1_mcart_1(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4))) )),
% 0.20/0.51    inference(superposition,[],[f28,f30])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f17,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f24,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK0 | ~r2_hidden(X8,sK4) | ~r2_hidden(X7,sK3) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (8561)------------------------------
% 0.20/0.51  % (8561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8561)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (8561)Memory used [KB]: 10746
% 0.20/0.51  % (8561)Time elapsed: 0.098 s
% 0.20/0.51  % (8561)------------------------------
% 0.20/0.51  % (8561)------------------------------
% 0.20/0.51  % (8575)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (8575)Refutation not found, incomplete strategy% (8575)------------------------------
% 0.20/0.51  % (8575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8553)Success in time 0.155 s
%------------------------------------------------------------------------------
