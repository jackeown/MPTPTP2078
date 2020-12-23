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
% DateTime   : Thu Dec  3 12:52:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 155 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  302 ( 682 expanded)
%              Number of equality atoms :  136 ( 310 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f73,f75,f104,f159,f171])).

fof(f171,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f81,f60])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_3 ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3(X0))
        | k1_xboole_0 != X0
        | sK1 != X0 )
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f78,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ v1_relat_1(sK3(X0))
        | sK1 != k1_relat_1(sK3(X0)) )
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f76,f41])).

fof(f76,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(sK3(X0))
        | ~ v1_relat_1(sK3(X0))
        | sK1 != k1_relat_1(sK3(X0)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK1 )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_3
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK1
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f159,plain,
    ( ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f81,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_5 ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_5 ),
    inference(superposition,[],[f108,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f108,plain,
    ( ! [X0] :
        ( sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0)))
        | k1_xboole_0 = X0 )
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0)))
        | k1_xboole_0 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f106,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0))) )
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0)))
        | sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0)))
        | k1_xboole_0 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f103,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2(X1,sK4(sK0,k1_xboole_0)))
        | k1_xboole_0 = X1
        | ~ v1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0)))
        | sK1 != k1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0))) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_5
  <=> ! [X1] :
        ( sK1 != k1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0)))
        | k1_xboole_0 = X1
        | ~ v1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0)))
        | ~ v1_funct_1(sK2(X1,sK4(sK0,k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f104,plain,
    ( spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f100,f54,f102])).

fof(f54,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f100,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | sK1 != k1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0)))
      | ~ v1_funct_1(sK2(X1,sK4(sK0,k1_xboole_0)))
      | ~ v1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0)))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f98,f89])).

fof(f89,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_funct_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f11])).

% (29597)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f98,plain,(
    ! [X1] :
      ( r1_tarski(k1_tarski(sK4(X1,k1_xboole_0)),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

% (29593)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f43,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f75,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f72,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_4
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f73,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f65,f70,f67])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f61,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f58,f54])).

fof(f30,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.52  % (29604)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (29596)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (29604)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (29610)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f61,f73,f75,f104,f159,f171])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    ~spl5_2 | ~spl5_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    $false | (~spl5_2 | ~spl5_3)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | (~spl5_2 | ~spl5_3)),
% 0.21/0.54    inference(superposition,[],[f81,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl5_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl5_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | ~spl5_3),
% 0.21/0.54    inference(equality_resolution,[],[f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f79,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(sK3(X0)) | k1_xboole_0 != X0 | sK1 != X0) ) | ~spl5_3),
% 0.21/0.54    inference(forward_demodulation,[],[f78,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != X0 | ~v1_relat_1(sK3(X0)) | sK1 != k1_relat_1(sK3(X0))) ) | ~spl5_3),
% 0.21/0.54    inference(forward_demodulation,[],[f76,f41])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | ~v1_relat_1(sK3(X0)) | sK1 != k1_relat_1(sK3(X0))) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f68,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK1) ) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl5_3 <=> ! [X0] : (k1_relat_1(X0) != sK1 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ~spl5_3 | ~spl5_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    $false | (~spl5_3 | ~spl5_5)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | (~spl5_3 | ~spl5_5)),
% 0.21/0.54    inference(superposition,[],[f81,f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl5_5),
% 0.21/0.54    inference(equality_resolution,[],[f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl5_5),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl5_5),
% 0.21/0.54    inference(superposition,[],[f108,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X0) ) | ~spl5_5),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X0) ) | ~spl5_5),
% 0.21/0.54    inference(resolution,[],[f106,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0)))) ) | ~spl5_5),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0))) | sK1 != k1_relat_1(sK2(X0,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X0) ) | ~spl5_5),
% 0.21/0.54    inference(resolution,[],[f103,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_1(sK2(X1,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X1 | ~v1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0))) | sK1 != k1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0)))) ) | ~spl5_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl5_5 <=> ! [X1] : (sK1 != k1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X1 | ~v1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0))) | ~v1_funct_1(sK2(X1,sK4(sK0,k1_xboole_0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl5_5 | spl5_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f100,f54,f102])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl5_1 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = sK0 | sK1 != k1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0))) | ~v1_funct_1(sK2(X1,sK4(sK0,k1_xboole_0))) | ~v1_relat_1(sK2(X1,sK4(sK0,k1_xboole_0))) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(resolution,[],[f98,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_funct_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 0.21/0.54    inference(superposition,[],[f31,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  % (29597)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k1_tarski(sK4(X1,k1_xboole_0)),X1) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(resolution,[],[f92,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.54  % (29593)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(resolution,[],[f44,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f43,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl5_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    $false | spl5_4),
% 0.21/0.54    inference(resolution,[],[f72,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,sK0) | spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    spl5_4 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl5_3 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f65,f70,f67])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f31,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ~spl5_1 | spl5_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f58,f54])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (29604)------------------------------
% 0.21/0.54  % (29604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29604)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (29604)Memory used [KB]: 6268
% 0.21/0.54  % (29604)Time elapsed: 0.122 s
% 0.21/0.54  % (29604)------------------------------
% 0.21/0.54  % (29604)------------------------------
% 0.21/0.55  % (29591)Success in time 0.177 s
%------------------------------------------------------------------------------
