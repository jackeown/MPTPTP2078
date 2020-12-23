%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:01 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  154 ( 268 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1621,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1614,f1617,f1620])).

fof(f1620,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1618])).

fof(f1618,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f1613,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1613,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f1611])).

fof(f1611,plain,
    ( spl5_8
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1617,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1615])).

fof(f1615,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f1609,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1609,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f1607])).

fof(f1607,plain,
    ( spl5_7
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1614,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1605,f1611,f1607])).

fof(f1605,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f1603,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1603,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f106,f1528])).

fof(f1528,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f296,f1527])).

fof(f1527,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f1461,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1461,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f221,f54])).

fof(f54,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f221,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k2_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11))) ),
    inference(superposition,[],[f38,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f296,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f244,f36])).

fof(f244,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f242,f34])).

fof(f242,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f38,f174])).

fof(f174,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f166,f34])).

fof(f166,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) = X0 ),
    inference(resolution,[],[f164,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f164,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) ),
    inference(resolution,[],[f163,f43])).

fof(f163,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f106,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(sK0,k4_xboole_0(X10,X11))
      | ~ r1_tarski(X10,k2_xboole_0(X11,sK1)) ) ),
    inference(resolution,[],[f46,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3926)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (3944)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (3936)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (3928)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (3947)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (3943)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (3924)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (3939)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (3935)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (3923)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (3922)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (3921)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (3937)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (3920)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (3925)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (3949)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (3948)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (3946)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (3950)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (3945)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (3940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (3938)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (3929)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (3942)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (3941)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (3931)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (3933)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (3934)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (3932)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (3930)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.11/0.64  % (3933)Refutation found. Thanks to Tanya!
% 2.11/0.64  % SZS status Theorem for theBenchmark
% 2.11/0.64  % SZS output start Proof for theBenchmark
% 2.11/0.64  fof(f1621,plain,(
% 2.11/0.64    $false),
% 2.11/0.64    inference(avatar_sat_refutation,[],[f1614,f1617,f1620])).
% 2.11/0.64  fof(f1620,plain,(
% 2.11/0.64    spl5_8),
% 2.11/0.64    inference(avatar_contradiction_clause,[],[f1618])).
% 2.11/0.64  fof(f1618,plain,(
% 2.11/0.64    $false | spl5_8),
% 2.11/0.64    inference(resolution,[],[f1613,f31])).
% 2.11/0.64  fof(f31,plain,(
% 2.11/0.64    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.64    inference(cnf_transformation,[],[f24])).
% 2.11/0.66  fof(f24,plain,(
% 2.11/0.66    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).
% 2.11/0.66  fof(f23,plain,(
% 2.11/0.66    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f16,plain,(
% 2.11/0.66    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.11/0.66    inference(flattening,[],[f15])).
% 2.11/0.66  fof(f15,plain,(
% 2.11/0.66    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.11/0.66    inference(ennf_transformation,[],[f13])).
% 2.11/0.66  fof(f13,negated_conjecture,(
% 2.11/0.66    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.11/0.66    inference(negated_conjecture,[],[f12])).
% 2.11/0.66  fof(f12,conjecture,(
% 2.11/0.66    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.11/0.66  fof(f1613,plain,(
% 2.11/0.66    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl5_8),
% 2.11/0.66    inference(avatar_component_clause,[],[f1611])).
% 2.11/0.66  fof(f1611,plain,(
% 2.11/0.66    spl5_8 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.11/0.66  fof(f1617,plain,(
% 2.11/0.66    spl5_7),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f1615])).
% 2.11/0.66  fof(f1615,plain,(
% 2.11/0.66    $false | spl5_7),
% 2.11/0.66    inference(resolution,[],[f1609,f70])).
% 2.11/0.66  fof(f70,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f69])).
% 2.11/0.66  fof(f69,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.11/0.66    inference(resolution,[],[f44,f43])).
% 2.11/0.66  fof(f43,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f30])).
% 2.11/0.66  fof(f30,plain,(
% 2.11/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 2.11/0.66  fof(f29,plain,(
% 2.11/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f28,plain,(
% 2.11/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.66    inference(rectify,[],[f27])).
% 2.11/0.66  fof(f27,plain,(
% 2.11/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.66    inference(nnf_transformation,[],[f19])).
% 2.11/0.66  fof(f19,plain,(
% 2.11/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f2])).
% 2.11/0.66  fof(f2,axiom,(
% 2.11/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.11/0.66  fof(f44,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f30])).
% 2.11/0.66  fof(f1609,plain,(
% 2.11/0.66    ~r1_tarski(sK0,sK0) | spl5_7),
% 2.11/0.66    inference(avatar_component_clause,[],[f1607])).
% 2.11/0.66  fof(f1607,plain,(
% 2.11/0.66    spl5_7 <=> r1_tarski(sK0,sK0)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.11/0.66  fof(f1614,plain,(
% 2.11/0.66    ~spl5_7 | ~spl5_8),
% 2.11/0.66    inference(avatar_split_clause,[],[f1605,f1611,f1607])).
% 2.11/0.66  fof(f1605,plain,(
% 2.11/0.66    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,sK0)),
% 2.11/0.66    inference(forward_demodulation,[],[f1603,f36])).
% 2.11/0.66  fof(f36,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f1])).
% 2.11/0.66  fof(f1,axiom,(
% 2.11/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.11/0.66  fof(f1603,plain,(
% 2.11/0.66    ~r1_tarski(sK0,sK0) | ~r1_tarski(sK0,k2_xboole_0(sK2,sK1))),
% 2.11/0.66    inference(superposition,[],[f106,f1528])).
% 2.11/0.66  fof(f1528,plain,(
% 2.11/0.66    sK0 = k4_xboole_0(sK0,sK2)),
% 2.11/0.66    inference(backward_demodulation,[],[f296,f1527])).
% 2.11/0.66  fof(f1527,plain,(
% 2.11/0.66    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.11/0.66    inference(forward_demodulation,[],[f1461,f34])).
% 2.11/0.66  fof(f34,plain,(
% 2.11/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.66    inference(cnf_transformation,[],[f5])).
% 2.11/0.66  fof(f5,axiom,(
% 2.11/0.66    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.11/0.66  fof(f1461,plain,(
% 2.11/0.66    ( ! [X2,X3] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.11/0.66    inference(superposition,[],[f221,f54])).
% 2.11/0.66  fof(f54,plain,(
% 2.11/0.66    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.11/0.66    inference(superposition,[],[f35,f36])).
% 2.11/0.66  fof(f35,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f10])).
% 2.11/0.66  fof(f10,axiom,(
% 2.11/0.66    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.11/0.66  fof(f221,plain,(
% 2.11/0.66    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k2_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11)))) )),
% 2.11/0.66    inference(superposition,[],[f38,f45])).
% 2.11/0.66  fof(f45,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f8])).
% 2.11/0.66  fof(f8,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.11/0.66  fof(f38,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f7])).
% 2.11/0.66  fof(f7,axiom,(
% 2.11/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.11/0.66  fof(f296,plain,(
% 2.11/0.66    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.11/0.66    inference(superposition,[],[f244,f36])).
% 2.11/0.66  fof(f244,plain,(
% 2.11/0.66    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 2.11/0.66    inference(forward_demodulation,[],[f242,f34])).
% 2.11/0.66  fof(f242,plain,(
% 2.11/0.66    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 2.11/0.66    inference(superposition,[],[f38,f174])).
% 2.11/0.66  fof(f174,plain,(
% 2.11/0.66    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.11/0.66    inference(superposition,[],[f166,f34])).
% 2.11/0.66  fof(f166,plain,(
% 2.11/0.66    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) = X0) )),
% 2.11/0.66    inference(resolution,[],[f164,f41])).
% 2.11/0.66  fof(f41,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.11/0.66    inference(cnf_transformation,[],[f18])).
% 2.11/0.66  fof(f18,plain,(
% 2.11/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.11/0.66    inference(ennf_transformation,[],[f4])).
% 2.11/0.66  fof(f4,axiom,(
% 2.11/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.11/0.66  fof(f164,plain,(
% 2.11/0.66    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0)) )),
% 2.11/0.66    inference(resolution,[],[f163,f43])).
% 2.11/0.66  fof(f163,plain,(
% 2.11/0.66    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 2.11/0.66    inference(resolution,[],[f48,f32])).
% 2.11/0.66  fof(f32,plain,(
% 2.11/0.66    r1_xboole_0(sK0,sK2)),
% 2.11/0.66    inference(cnf_transformation,[],[f24])).
% 2.11/0.66  fof(f48,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.11/0.66    inference(definition_unfolding,[],[f40,f37])).
% 2.11/0.66  fof(f37,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f11])).
% 2.11/0.66  fof(f11,axiom,(
% 2.11/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.11/0.66  fof(f40,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f26])).
% 2.11/0.66  fof(f26,plain,(
% 2.11/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f25])).
% 2.11/0.66  fof(f25,plain,(
% 2.11/0.66    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f17,plain,(
% 2.11/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/0.66    inference(ennf_transformation,[],[f14])).
% 2.11/0.66  fof(f14,plain,(
% 2.11/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/0.66    inference(rectify,[],[f3])).
% 2.11/0.66  fof(f3,axiom,(
% 2.11/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.11/0.66  fof(f106,plain,(
% 2.11/0.66    ( ! [X10,X11] : (~r1_tarski(sK0,k4_xboole_0(X10,X11)) | ~r1_tarski(X10,k2_xboole_0(X11,sK1))) )),
% 2.11/0.66    inference(resolution,[],[f46,f95])).
% 2.11/0.66  fof(f95,plain,(
% 2.11/0.66    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) )),
% 2.11/0.66    inference(resolution,[],[f47,f33])).
% 2.11/0.66  fof(f33,plain,(
% 2.11/0.66    ~r1_tarski(sK0,sK1)),
% 2.11/0.66    inference(cnf_transformation,[],[f24])).
% 2.11/0.66  fof(f47,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f22])).
% 2.11/0.66  fof(f22,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.11/0.66    inference(flattening,[],[f21])).
% 2.11/0.66  fof(f21,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.11/0.66    inference(ennf_transformation,[],[f6])).
% 2.11/0.66  fof(f6,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.11/0.66  fof(f46,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f20])).
% 2.11/0.66  fof(f20,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.11/0.66    inference(ennf_transformation,[],[f9])).
% 2.11/0.66  fof(f9,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.11/0.66  % SZS output end Proof for theBenchmark
% 2.11/0.66  % (3933)------------------------------
% 2.11/0.66  % (3933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.66  % (3933)Termination reason: Refutation
% 2.11/0.66  
% 2.11/0.66  % (3933)Memory used [KB]: 7291
% 2.11/0.66  % (3933)Time elapsed: 0.240 s
% 2.11/0.66  % (3933)------------------------------
% 2.11/0.66  % (3933)------------------------------
% 2.11/0.66  % (3917)Success in time 0.309 s
%------------------------------------------------------------------------------
