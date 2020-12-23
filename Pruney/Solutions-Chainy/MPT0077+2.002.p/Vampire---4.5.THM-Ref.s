%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 219 expanded)
%              Number of leaves         :   16 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 501 expanded)
%              Number of equality atoms :   30 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f654,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f166,f181,f192,f351,f652])).

fof(f652,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f82,f636])).

fof(f636,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f635,f412])).

fof(f412,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f396,f47])).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f396,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))
    | ~ spl6_2 ),
    inference(superposition,[],[f362,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f362,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f82,f82,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f635,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f626,f556])).

fof(f556,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f546,f47])).

fof(f546,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f51,f452])).

fof(f452,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f353,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f353,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f63,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f626,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl6_1
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f382,f617])).

fof(f617,plain,
    ( ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(sK1,X2))
    | ~ spl6_3 ),
    inference(superposition,[],[f33,f595])).

fof(f595,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f585,f47])).

fof(f585,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(superposition,[],[f51,f487])).

fof(f487,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f355,f43])).

fof(f355,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f165,f50])).

fof(f165,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f382,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_1
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f82,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f65,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f65,f43])).

fof(f65,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f63,f50])).

fof(f351,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f59,f260,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f260,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(X0,sK2),sK0)
    | spl6_2 ),
    inference(superposition,[],[f199,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f199,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK2,X0),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f36,f194,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f194,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f62,f29])).

fof(f62,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f59,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f192,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl6_1
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f171,f164,f29])).

fof(f164,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f171,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f36,f168,f28])).

fof(f168,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f59,f29])).

fof(f181,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f57,f163,f61])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f166,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f27,f163,f57])).

fof(f27,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f26,f61,f57])).

fof(f26,plain,
    ( r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (14556)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (14548)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (14538)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (14540)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (14539)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (14543)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (14556)Refutation not found, incomplete strategy% (14556)------------------------------
% 0.22/0.53  % (14556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14556)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14556)Memory used [KB]: 10618
% 0.22/0.53  % (14556)Time elapsed: 0.069 s
% 0.22/0.53  % (14556)------------------------------
% 0.22/0.53  % (14556)------------------------------
% 0.22/0.54  % (14545)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (14557)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (14560)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (14535)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (14561)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (14541)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (14536)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (14537)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (14534)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (14534)Refutation not found, incomplete strategy% (14534)------------------------------
% 0.22/0.55  % (14534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14534)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14534)Memory used [KB]: 1663
% 0.22/0.55  % (14534)Time elapsed: 0.135 s
% 0.22/0.55  % (14534)------------------------------
% 0.22/0.55  % (14534)------------------------------
% 0.22/0.55  % (14536)Refutation not found, incomplete strategy% (14536)------------------------------
% 0.22/0.55  % (14536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14536)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14536)Memory used [KB]: 10746
% 0.22/0.55  % (14536)Time elapsed: 0.137 s
% 0.22/0.55  % (14536)------------------------------
% 0.22/0.55  % (14536)------------------------------
% 0.22/0.55  % (14543)Refutation not found, incomplete strategy% (14543)------------------------------
% 0.22/0.55  % (14543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14543)Memory used [KB]: 10618
% 0.22/0.55  % (14543)Time elapsed: 0.135 s
% 0.22/0.55  % (14543)------------------------------
% 0.22/0.55  % (14543)------------------------------
% 0.22/0.55  % (14544)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (14549)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (14544)Refutation not found, incomplete strategy% (14544)------------------------------
% 0.22/0.55  % (14544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14544)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14544)Memory used [KB]: 10618
% 0.22/0.55  % (14544)Time elapsed: 0.134 s
% 0.22/0.55  % (14544)------------------------------
% 0.22/0.55  % (14544)------------------------------
% 0.22/0.55  % (14563)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (14558)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (14552)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (14550)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (14559)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (14551)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (14555)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (14553)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (14546)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (14542)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (14551)Refutation not found, incomplete strategy% (14551)------------------------------
% 0.22/0.56  % (14551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14547)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.57  % (14542)Refutation not found, incomplete strategy% (14542)------------------------------
% 0.22/0.57  % (14542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14542)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (14542)Memory used [KB]: 10746
% 0.22/0.57  % (14542)Time elapsed: 0.158 s
% 0.22/0.57  % (14542)------------------------------
% 0.22/0.57  % (14542)------------------------------
% 0.22/0.57  % (14551)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (14551)Memory used [KB]: 10618
% 0.22/0.57  % (14551)Time elapsed: 0.160 s
% 0.22/0.57  % (14551)------------------------------
% 0.22/0.57  % (14551)------------------------------
% 0.22/0.57  % (14538)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f654,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f64,f166,f181,f192,f351,f652])).
% 0.22/0.57  fof(f652,plain,(
% 0.22/0.57    spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f645])).
% 0.22/0.57  fof(f645,plain,(
% 0.22/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f82,f636])).
% 0.22/0.57  fof(f636,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f635,f412])).
% 0.22/0.57  fof(f412,plain,(
% 0.22/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl6_2),
% 0.22/0.57    inference(forward_demodulation,[],[f396,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.57  fof(f396,plain,(
% 0.22/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ) | ~spl6_2),
% 0.22/0.57    inference(superposition,[],[f362,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f46,f45,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.57  fof(f362,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl6_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f82,f82,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.57  fof(f635,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f626,f556])).
% 0.22/0.57  fof(f556,plain,(
% 0.22/0.57    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_2),
% 0.22/0.57    inference(forward_demodulation,[],[f546,f47])).
% 0.22/0.57  fof(f546,plain,(
% 0.22/0.57    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 0.22/0.57    inference(superposition,[],[f51,f452])).
% 0.22/0.57  fof(f452,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f353,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.57  fof(f353,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ) | ~spl6_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f63,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f30,f45])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    r1_xboole_0(sK0,sK2) | ~spl6_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    spl6_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f44,f45])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.57  fof(f626,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (spl6_1 | ~spl6_3)),
% 0.22/0.57    inference(backward_demodulation,[],[f382,f617])).
% 0.22/0.57  fof(f617,plain,(
% 0.22/0.57    ( ! [X2] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(sK1,X2))) ) | ~spl6_3),
% 0.22/0.57    inference(superposition,[],[f33,f595])).
% 0.22/0.57  fof(f595,plain,(
% 0.22/0.57    sK0 = k4_xboole_0(sK0,sK1) | ~spl6_3),
% 0.22/0.57    inference(forward_demodulation,[],[f585,f47])).
% 0.22/0.57  fof(f585,plain,(
% 0.22/0.57    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_3),
% 0.22/0.57    inference(superposition,[],[f51,f487])).
% 0.22/0.57  fof(f487,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f355,f43])).
% 0.22/0.57  fof(f355,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f165,f50])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    r1_xboole_0(sK0,sK1) | ~spl6_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f163])).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    spl6_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.57  fof(f382,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) | spl6_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f58,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f31,f45])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl6_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    spl6_1 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_2),
% 0.22/0.57    inference(backward_demodulation,[],[f65,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f65,f43])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ) | ~spl6_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f63,f50])).
% 0.22/0.58  fof(f351,plain,(
% 0.22/0.58    ~spl6_1 | spl6_2),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f341])).
% 0.22/0.58  fof(f341,plain,(
% 0.22/0.58    $false | (~spl6_1 | spl6_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f59,f260,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.58  fof(f260,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(X0,sK2),sK0)) ) | spl6_2),
% 0.22/0.58    inference(superposition,[],[f199,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.58  fof(f199,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK2,X0),sK0)) ) | spl6_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f36,f194,f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.58    inference(flattening,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.58  fof(f194,plain,(
% 0.22/0.58    ~r1_xboole_0(sK2,sK0) | spl6_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f62,f29])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ~r1_xboole_0(sK0,sK2) | spl6_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f61])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,axiom,(
% 0.22/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl6_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f57])).
% 0.22/0.58  fof(f192,plain,(
% 0.22/0.58    ~spl6_1 | spl6_3),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f185])).
% 0.22/0.58  fof(f185,plain,(
% 0.22/0.58    $false | (~spl6_1 | spl6_3)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f171,f164,f29])).
% 0.22/0.58  fof(f164,plain,(
% 0.22/0.58    ~r1_xboole_0(sK0,sK1) | spl6_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f163])).
% 0.22/0.58  fof(f171,plain,(
% 0.22/0.58    r1_xboole_0(sK1,sK0) | ~spl6_1),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f36,f168,f28])).
% 0.22/0.58  fof(f168,plain,(
% 0.22/0.58    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f59,f29])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    ~spl6_2 | ~spl6_3 | ~spl6_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f25,f57,f163,f61])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.58    inference(ennf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.58    inference(negated_conjecture,[],[f16])).
% 0.22/0.58  fof(f16,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.58  fof(f166,plain,(
% 0.22/0.58    spl6_1 | spl6_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f27,f163,f57])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    spl6_1 | spl6_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f26,f61,f57])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    r1_xboole_0(sK0,sK2) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (14538)------------------------------
% 0.22/0.58  % (14538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (14538)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (14538)Memory used [KB]: 6396
% 0.22/0.58  % (14538)Time elapsed: 0.145 s
% 0.22/0.58  % (14538)------------------------------
% 0.22/0.58  % (14538)------------------------------
% 0.22/0.58  % (14532)Success in time 0.207 s
%------------------------------------------------------------------------------
