%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:15 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   51 (  94 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 ( 448 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f158,f27])).

fof(f27,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK3))
    & r2_hidden(sK2,k2_relat_1(k5_relat_1(sK4,sK3)))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X0,k2_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK2,k2_relat_1(sK3))
          & r2_hidden(sK2,k2_relat_1(k5_relat_1(X2,sK3)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r2_hidden(sK2,k2_relat_1(sK3))
        & r2_hidden(sK2,k2_relat_1(k5_relat_1(X2,sK3)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(sK2,k2_relat_1(sK3))
      & r2_hidden(sK2,k2_relat_1(k5_relat_1(sK4,sK3)))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(f158,plain,(
    ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f157,f25])).

fof(f25,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f157,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f151,f30])).

fof(f30,plain,(
    ~ r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f151,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f106,f29])).

fof(f29,plain,(
    r2_hidden(sK2,k2_relat_1(k5_relat_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f103,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f102,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ sP0(X1,X2,X0) ) ),
    inference(resolution,[],[f89,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k4_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f12,f11])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X4,X5,X3] :
      ( sP0(k4_xboole_0(X4,X5),X3,X4)
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f34,f53])).

fof(f53,plain,(
    ! [X4,X3] :
      ( sP1(X3,k4_xboole_0(X3,X4),X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (31832)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31840)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (31839)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (31843)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (31830)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31831)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31835)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (31851)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (31838)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (31834)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31851)Refutation not found, incomplete strategy% (31851)------------------------------
% 0.21/0.54  % (31851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31851)Memory used [KB]: 10618
% 0.21/0.54  % (31851)Time elapsed: 0.120 s
% 0.21/0.54  % (31851)------------------------------
% 0.21/0.54  % (31851)------------------------------
% 0.21/0.54  % (31833)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (31857)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.54  % (31850)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (31855)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.55  % (31842)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (31854)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.55  % (31831)Refutation not found, incomplete strategy% (31831)------------------------------
% 1.45/0.55  % (31831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (31831)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (31831)Memory used [KB]: 10618
% 1.45/0.55  % (31831)Time elapsed: 0.133 s
% 1.45/0.55  % (31831)------------------------------
% 1.45/0.55  % (31831)------------------------------
% 1.45/0.55  % (31849)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (31856)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (31847)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (31846)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (31829)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.55  % (31856)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f159,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(subsumption_resolution,[],[f158,f27])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    v1_relat_1(sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f16])).
% 1.45/0.55  fof(f16,plain,(
% 1.45/0.55    (~r2_hidden(sK2,k2_relat_1(sK3)) & r2_hidden(sK2,k2_relat_1(k5_relat_1(sK4,sK3))) & v1_funct_1(sK4) & v1_relat_1(sK4)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f15,f14])).
% 1.45/0.55  fof(f14,plain,(
% 1.45/0.55    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(sK2,k2_relat_1(sK3)) & r2_hidden(sK2,k2_relat_1(k5_relat_1(X2,sK3))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f15,plain,(
% 1.45/0.55    ? [X2] : (~r2_hidden(sK2,k2_relat_1(sK3)) & r2_hidden(sK2,k2_relat_1(k5_relat_1(X2,sK3))) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r2_hidden(sK2,k2_relat_1(sK3)) & r2_hidden(sK2,k2_relat_1(k5_relat_1(sK4,sK3))) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f8,plain,(
% 1.45/0.55    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.45/0.55    inference(flattening,[],[f7])).
% 1.45/0.55  fof(f7,plain,(
% 1.45/0.55    ? [X0,X1] : (? [X2] : ((~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.45/0.55    inference(ennf_transformation,[],[f6])).
% 1.45/0.55  fof(f6,negated_conjecture,(
% 1.45/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 1.45/0.55    inference(negated_conjecture,[],[f5])).
% 1.45/0.55  fof(f5,conjecture,(
% 1.45/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).
% 1.45/0.55  fof(f158,plain,(
% 1.45/0.55    ~v1_relat_1(sK4)),
% 1.45/0.55    inference(subsumption_resolution,[],[f157,f25])).
% 1.45/0.55  fof(f25,plain,(
% 1.45/0.55    v1_relat_1(sK3)),
% 1.45/0.55    inference(cnf_transformation,[],[f16])).
% 1.45/0.55  fof(f157,plain,(
% 1.45/0.55    ~v1_relat_1(sK3) | ~v1_relat_1(sK4)),
% 1.45/0.55    inference(subsumption_resolution,[],[f151,f30])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ~r2_hidden(sK2,k2_relat_1(sK3))),
% 1.45/0.55    inference(cnf_transformation,[],[f16])).
% 1.45/0.55  fof(f151,plain,(
% 1.45/0.55    r2_hidden(sK2,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK4)),
% 1.45/0.55    inference(resolution,[],[f106,f29])).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    r2_hidden(sK2,k2_relat_1(k5_relat_1(sK4,sK3)))),
% 1.45/0.55    inference(cnf_transformation,[],[f16])).
% 1.45/0.55  fof(f106,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) | r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 1.45/0.55    inference(resolution,[],[f103,f31])).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f9])).
% 1.45/0.55  fof(f9,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.45/0.55  fof(f103,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.55    inference(resolution,[],[f102,f40])).
% 1.45/0.55  fof(f40,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f23])).
% 1.45/0.55  fof(f23,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.45/0.55    inference(rectify,[],[f22])).
% 1.45/0.55  fof(f22,plain,(
% 1.45/0.55    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.45/0.55    inference(flattening,[],[f21])).
% 1.45/0.55  fof(f21,plain,(
% 1.45/0.55    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.45/0.55    inference(nnf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,plain,(
% 1.45/0.55    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.45/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/0.55  fof(f102,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~sP0(X1,X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f96,f38])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f23])).
% 1.45/0.55  fof(f96,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | ~sP0(X1,X2,X0)) )),
% 1.45/0.55    inference(resolution,[],[f89,f58])).
% 1.45/0.55  fof(f58,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (r2_hidden(X1,k4_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 1.45/0.55    inference(resolution,[],[f35,f44])).
% 1.45/0.55  fof(f44,plain,(
% 1.45/0.55    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.45/0.55    inference(equality_resolution,[],[f41])).
% 1.45/0.55  fof(f41,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.55    inference(cnf_transformation,[],[f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.55    inference(nnf_transformation,[],[f13])).
% 1.45/0.55  fof(f13,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.45/0.55    inference(definition_folding,[],[f1,f12,f11])).
% 1.45/0.55  fof(f12,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.45/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.45/0.55  fof(f35,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f20])).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 1.45/0.55  fof(f19,plain,(
% 1.45/0.55    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f18,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.45/0.55    inference(rectify,[],[f17])).
% 1.45/0.55  fof(f17,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.45/0.55    inference(nnf_transformation,[],[f12])).
% 1.45/0.55  fof(f89,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X1,X2) | ~r2_hidden(X0,X1)) )),
% 1.45/0.55    inference(resolution,[],[f57,f39])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f23])).
% 1.45/0.55  fof(f57,plain,(
% 1.45/0.55    ( ! [X4,X5,X3] : (sP0(k4_xboole_0(X4,X5),X3,X4) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,X5)) )),
% 1.45/0.55    inference(resolution,[],[f34,f53])).
% 1.45/0.55  fof(f53,plain,(
% 1.45/0.55    ( ! [X4,X3] : (sP1(X3,k4_xboole_0(X3,X4),X3) | ~r1_tarski(X3,X4)) )),
% 1.45/0.55    inference(superposition,[],[f44,f43])).
% 1.45/0.55  fof(f43,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f33,f32])).
% 1.45/0.55  fof(f32,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f3])).
% 1.45/0.55  fof(f3,axiom,(
% 1.45/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,plain,(
% 1.45/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.45/0.55    inference(ennf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.45/0.55  fof(f34,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f20])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (31856)------------------------------
% 1.45/0.55  % (31856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (31856)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (31856)Memory used [KB]: 6268
% 1.45/0.55  % (31856)Time elapsed: 0.143 s
% 1.45/0.55  % (31856)------------------------------
% 1.45/0.55  % (31856)------------------------------
% 1.45/0.56  % (31841)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.56  % (31848)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.56  % (31853)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (31828)Success in time 0.199 s
%------------------------------------------------------------------------------
