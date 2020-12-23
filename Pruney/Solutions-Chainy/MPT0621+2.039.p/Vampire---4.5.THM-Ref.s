%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 134 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  237 ( 643 expanded)
%              Number of equality atoms :  118 ( 302 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f230,f259])).

fof(f259,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f251,f234])).

fof(f234,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl4_5 ),
    inference(superposition,[],[f134,f134])).

fof(f134,plain,
    ( ! [X1] : k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_5
  <=> ! [X1] : k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f251,plain,
    ( ! [X0] : k1_xboole_0 != X0
    | ~ spl4_5 ),
    inference(superposition,[],[f24,f234])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f230,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f222,f137])).

fof(f137,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl4_4 ),
    inference(superposition,[],[f131,f131])).

fof(f131,plain,
    ( ! [X2] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_4
  <=> ! [X2] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f222,plain,
    ( ! [X0] : k1_xboole_0 != X0
    | ~ spl4_4 ),
    inference(superposition,[],[f24,f137])).

fof(f135,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f128,f133,f130])).

fof(f128,plain,(
    ! [X2,X1] :
      ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1
      | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2 ) ),
    inference(subsumption_resolution,[],[f126,f24])).

fof(f126,plain,(
    ! [X2,X1] :
      ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2 ) ),
    inference(superposition,[],[f122,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = sK3(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK3(X0,X1) ) ),
    inference(superposition,[],[f68,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f68,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relat_1(sK3(X1,X2))
      | k1_xboole_0 = sK3(X1,X2) ) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(sK3(X1,X2),sK2(X1,sK0)) = X2
      | sK0 = X1
      | k1_funct_1(sK1(sK0),sK2(X1,sK0)) = X0 ) ),
    inference(superposition,[],[f115,f52])).

fof(f52,plain,(
    ! [X0] : sK1(sK0) = sK3(sK0,X0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK0 != X1
      | sK1(X1) = sK3(sK0,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK3(X0,X1) = sK1(X2)
      | sK0 != X2 ) ),
    inference(superposition,[],[f46,f35])).

fof(f46,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK3(X2,X3))
      | sK3(X2,X3) = sK1(X4)
      | sK0 != X4 ) ),
    inference(subsumption_resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK3(X2,X3))
      | sK3(X2,X3) = sK1(X4)
      | sK0 != X4
      | ~ v1_relat_1(sK3(X2,X3)) ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != sK0
      | sK1(X0) = X1
      | sK0 != X0
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f39,f29])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | sK1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | sK1(X0) = X1
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | X1 = X2
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,(
    ! [X4,X2,X5,X3] :
      ( k1_funct_1(sK3(X3,X4),sK2(X2,X3)) = X4
      | X2 = X3
      | k1_funct_1(sK3(X2,X5),sK2(X2,X3)) = X5 ) ),
    inference(resolution,[],[f105,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK3(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | X0 = X1
      | k1_funct_1(sK3(X1,X2),sK2(X0,X1)) = X2 ) ),
    inference(resolution,[],[f31,f36])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (25207)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (25199)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (25195)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (25191)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (25203)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (25195)Refutation not found, incomplete strategy% (25195)------------------------------
% 0.20/0.51  % (25195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25195)Memory used [KB]: 10618
% 0.20/0.51  % (25195)Time elapsed: 0.101 s
% 0.20/0.51  % (25195)------------------------------
% 0.20/0.51  % (25195)------------------------------
% 0.20/0.51  % (25211)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (25189)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (25211)Refutation not found, incomplete strategy% (25211)------------------------------
% 0.20/0.52  % (25211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25211)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25211)Memory used [KB]: 10618
% 0.20/0.52  % (25211)Time elapsed: 0.105 s
% 0.20/0.52  % (25211)------------------------------
% 0.20/0.52  % (25211)------------------------------
% 0.20/0.52  % (25189)Refutation not found, incomplete strategy% (25189)------------------------------
% 0.20/0.52  % (25189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25189)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25189)Memory used [KB]: 6268
% 0.20/0.52  % (25189)Time elapsed: 0.111 s
% 0.20/0.52  % (25189)------------------------------
% 0.20/0.52  % (25189)------------------------------
% 0.20/0.53  % (25186)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (25197)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (25185)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (25188)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (25185)Refutation not found, incomplete strategy% (25185)------------------------------
% 0.20/0.53  % (25185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25185)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25185)Memory used [KB]: 1663
% 0.20/0.53  % (25185)Time elapsed: 0.115 s
% 0.20/0.53  % (25185)------------------------------
% 0.20/0.53  % (25185)------------------------------
% 0.20/0.53  % (25187)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (25205)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (25205)Refutation not found, incomplete strategy% (25205)------------------------------
% 0.20/0.53  % (25205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25205)Memory used [KB]: 10746
% 0.20/0.53  % (25205)Time elapsed: 0.133 s
% 0.20/0.53  % (25205)------------------------------
% 0.20/0.53  % (25205)------------------------------
% 0.20/0.53  % (25193)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (25214)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (25208)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (25213)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (25210)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (25196)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (25190)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (25196)Refutation not found, incomplete strategy% (25196)------------------------------
% 0.20/0.54  % (25196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25196)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25196)Memory used [KB]: 10618
% 0.20/0.54  % (25196)Time elapsed: 0.125 s
% 0.20/0.54  % (25196)------------------------------
% 0.20/0.54  % (25196)------------------------------
% 0.20/0.54  % (25210)Refutation not found, incomplete strategy% (25210)------------------------------
% 0.20/0.54  % (25210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25210)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25210)Memory used [KB]: 6268
% 0.20/0.54  % (25210)Time elapsed: 0.129 s
% 0.20/0.54  % (25210)------------------------------
% 0.20/0.54  % (25210)------------------------------
% 0.20/0.54  % (25200)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (25212)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (25202)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (25202)Refutation not found, incomplete strategy% (25202)------------------------------
% 0.20/0.54  % (25202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25202)Memory used [KB]: 10618
% 0.20/0.54  % (25202)Time elapsed: 0.137 s
% 0.20/0.54  % (25202)------------------------------
% 0.20/0.54  % (25202)------------------------------
% 0.20/0.54  % (25201)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (25192)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (25206)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (25194)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (25194)Refutation not found, incomplete strategy% (25194)------------------------------
% 0.20/0.55  % (25194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25194)Memory used [KB]: 10618
% 0.20/0.55  % (25194)Time elapsed: 0.139 s
% 0.20/0.55  % (25194)------------------------------
% 0.20/0.55  % (25194)------------------------------
% 0.20/0.55  % (25206)Refutation not found, incomplete strategy% (25206)------------------------------
% 0.20/0.55  % (25206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25206)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25206)Memory used [KB]: 1663
% 0.20/0.55  % (25206)Time elapsed: 0.139 s
% 0.20/0.55  % (25206)------------------------------
% 0.20/0.55  % (25206)------------------------------
% 0.20/0.55  % (25209)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (25198)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (25204)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (25188)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f260,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f135,f230,f259])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    ~spl4_5),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f258])).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    $false | ~spl4_5),
% 0.20/0.55    inference(subsumption_resolution,[],[f251,f234])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 = X1) ) | ~spl4_5),
% 0.20/0.55    inference(superposition,[],[f134,f134])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1) ) | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f133])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    spl4_5 <=> ! [X1] : k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f251,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != X0) ) | ~spl4_5),
% 0.20/0.55    inference(superposition,[],[f24,f234])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f8,plain,(
% 0.20/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(flattening,[],[f7])).
% 0.20/0.55  fof(f7,plain,(
% 0.20/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.55    inference(negated_conjecture,[],[f5])).
% 0.20/0.55  fof(f5,conjecture,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ~spl4_4),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f229])).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    $false | ~spl4_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f222,f137])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 = X1) ) | ~spl4_4),
% 0.20/0.55    inference(superposition,[],[f131,f131])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    ( ! [X2] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2) ) | ~spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f130])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    spl4_4 <=> ! [X2] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != X0) ) | ~spl4_4),
% 0.20/0.55    inference(superposition,[],[f24,f137])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl4_4 | spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f128,f133,f130])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ( ! [X2,X1] : (k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1 | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f126,f24])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ( ! [X2,X1] : (k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X1 | k1_xboole_0 = sK0 | k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2) )),
% 0.20/0.55    inference(superposition,[],[f122,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = sK3(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK3(X0,X1)) )),
% 0.20/0.55    inference(superposition,[],[f68,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X1] : (k1_xboole_0 != k1_relat_1(sK3(X1,X2)) | k1_xboole_0 = sK3(X1,X2)) )),
% 0.20/0.55    inference(resolution,[],[f25,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_funct_1(sK3(X1,X2),sK2(X1,sK0)) = X2 | sK0 = X1 | k1_funct_1(sK1(sK0),sK2(X1,sK0)) = X0) )),
% 0.20/0.55    inference(superposition,[],[f115,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0] : (sK1(sK0) = sK3(sK0,X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK0 != X1 | sK1(X1) = sK3(sK0,X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (sK0 != X0 | sK3(X0,X1) = sK1(X2) | sK0 != X2) )),
% 0.20/0.55    inference(superposition,[],[f46,f35])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK3(X2,X3)) | sK3(X2,X3) = sK1(X4) | sK0 != X4) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f44,f33])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK3(X2,X3)) | sK3(X2,X3) = sK1(X4) | sK0 != X4 | ~v1_relat_1(sK3(X2,X3))) )),
% 0.20/0.55    inference(resolution,[],[f40,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X1) != sK0 | sK1(X0) = X1 | sK0 != X0 | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f39,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK0 != k1_relat_1(sK1(X0)) | k1_relat_1(X1) != sK0 | sK1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f37,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK0 != k1_relat_1(sK1(X0)) | k1_relat_1(X1) != sK0 | sK1(X0) = X1 | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(resolution,[],[f23,f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | X1 = X2 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ( ! [X4,X2,X5,X3] : (k1_funct_1(sK3(X3,X4),sK2(X2,X3)) = X4 | X2 = X3 | k1_funct_1(sK3(X2,X5),sK2(X2,X3)) = X5) )),
% 0.20/0.55    inference(resolution,[],[f105,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK3(X0,X1),X3) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1),X0) | X0 = X1 | k1_funct_1(sK3(X1,X2),sK2(X0,X1)) = X2) )),
% 0.20/0.55    inference(resolution,[],[f31,f36])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.20/0.55    inference(nnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (25188)------------------------------
% 0.20/0.55  % (25188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25188)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (25188)Memory used [KB]: 10874
% 0.20/0.55  % (25188)Time elapsed: 0.131 s
% 0.20/0.55  % (25188)------------------------------
% 0.20/0.55  % (25188)------------------------------
% 0.20/0.55  % (25184)Success in time 0.194 s
%------------------------------------------------------------------------------
