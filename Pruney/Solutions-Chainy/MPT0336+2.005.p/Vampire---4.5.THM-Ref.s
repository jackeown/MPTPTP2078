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
% DateTime   : Thu Dec  3 12:43:23 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 149 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  181 ( 348 expanded)
%              Number of equality atoms :   84 ( 137 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f766,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f413,f633,f765])).

fof(f765,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f71,f701])).

fof(f701,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f691,f104])).

fof(f104,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f91,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f91,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f25,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f691,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f222,f686])).

fof(f686,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k2_xboole_0(sK0,X0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f674,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f674,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f667,f31])).

fof(f667,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f408,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f408,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl6_1
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f222,plain,(
    ~ r2_hidden(k1_xboole_0,k1_enumset1(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f218,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f218,plain,(
    ~ r2_hidden(k1_xboole_0,k1_enumset1(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f113,f113,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f113,plain,(
    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f26,f29])).

fof(f26,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f633,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f35,f602,f30])).

fof(f602,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f535,f104])).

fof(f535,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl6_2 ),
    inference(superposition,[],[f420,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f420,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl6_2 ),
    inference(superposition,[],[f161,f412])).

fof(f412,plain,
    ( k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl6_2
  <=> k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f161,plain,(
    ! [X0] : k1_xboole_0 != k3_xboole_0(k1_enumset1(X0,X0,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f87,f29])).

fof(f87,plain,(
    ! [X0] : ~ r1_xboole_0(k1_enumset1(X0,X0,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f71,f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f24,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f413,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f115,f410,f406])).

fof(f115,plain,
    ( k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f56,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_enumset1(X0,X0,X0) = X3
      | k1_enumset1(X1,X1,X1) = X3
      | k1_enumset1(X2,X2,X2) = X3
      | k1_enumset1(X0,X0,X1) = X3
      | k1_enumset1(X1,X1,X2) = X3
      | k1_enumset1(X0,X0,X2) = X3
      | k1_enumset1(X0,X1,X2) = X3
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f42,f55,f55,f55,f54,f54,f54])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X3
      | k1_tarski(X0) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X2) = X3
      | k2_tarski(X0,X1) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k1_enumset1(X0,X1,X2) = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f56,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f23,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (29898)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (29876)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (29883)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (29885)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (29877)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (29890)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (29874)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (29873)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (29891)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (29888)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (29872)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (29900)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (29899)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (29892)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (29875)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (29894)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (29889)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (29886)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (29878)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (29893)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (29896)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (29884)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (29880)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (29879)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (29882)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (29895)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (29900)Refutation not found, incomplete strategy% (29900)------------------------------
% 0.20/0.54  % (29900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29900)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29900)Memory used [KB]: 1663
% 0.20/0.54  % (29900)Time elapsed: 0.145 s
% 0.20/0.54  % (29900)------------------------------
% 0.20/0.54  % (29900)------------------------------
% 0.20/0.54  % (29897)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (29881)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.54/0.57  % (29871)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.54/0.58  % (29887)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.73/0.59  % (29896)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f766,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(avatar_sat_refutation,[],[f413,f633,f765])).
% 1.73/0.59  fof(f765,plain,(
% 1.73/0.59    ~spl6_1),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f760])).
% 1.73/0.59  fof(f760,plain,(
% 1.73/0.59    $false | ~spl6_1),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f71,f701])).
% 1.73/0.59  fof(f701,plain,(
% 1.73/0.59    ~r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl6_1),
% 1.73/0.59    inference(forward_demodulation,[],[f691,f104])).
% 1.73/0.59  fof(f104,plain,(
% 1.73/0.59    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f91,f30])).
% 1.73/0.59  fof(f30,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.73/0.59  fof(f91,plain,(
% 1.73/0.59    r1_xboole_0(sK1,sK2)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f25,f31])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,plain,(
% 1.73/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    r1_xboole_0(sK2,sK1)),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,plain,(
% 1.73/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.73/0.59    inference(flattening,[],[f17])).
% 1.73/0.59  fof(f17,plain,(
% 1.73/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.73/0.59    inference(ennf_transformation,[],[f15])).
% 1.73/0.59  fof(f15,negated_conjecture,(
% 1.73/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.73/0.59    inference(negated_conjecture,[],[f14])).
% 1.73/0.59  fof(f14,conjecture,(
% 1.73/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.73/0.59  fof(f691,plain,(
% 1.73/0.59    ~r2_hidden(k1_xboole_0,k1_enumset1(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | ~spl6_1),
% 1.73/0.59    inference(backward_demodulation,[],[f222,f686])).
% 1.73/0.59  fof(f686,plain,(
% 1.73/0.59    ( ! [X0] : (k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k2_xboole_0(sK0,X0))) ) | ~spl6_1),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f674,f27])).
% 1.73/0.59  fof(f27,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f19])).
% 1.73/0.59  fof(f19,plain,(
% 1.73/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f8])).
% 1.73/0.59  fof(f8,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.73/0.59  fof(f674,plain,(
% 1.73/0.59    r1_xboole_0(sK1,sK0) | ~spl6_1),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f667,f31])).
% 1.73/0.59  fof(f667,plain,(
% 1.73/0.59    r1_xboole_0(sK0,sK1) | ~spl6_1),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f408,f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f3])).
% 1.73/0.59  fof(f408,plain,(
% 1.73/0.59    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl6_1),
% 1.73/0.59    inference(avatar_component_clause,[],[f406])).
% 1.73/0.59  fof(f406,plain,(
% 1.73/0.59    spl6_1 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.73/0.59  fof(f222,plain,(
% 1.73/0.59    ~r2_hidden(k1_xboole_0,k1_enumset1(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))))),
% 1.73/0.59    inference(forward_demodulation,[],[f218,f53])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f2])).
% 1.73/0.59  fof(f2,axiom,(
% 1.73/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.73/0.59  fof(f218,plain,(
% 1.73/0.59    ~r2_hidden(k1_xboole_0,k1_enumset1(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)))),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f113,f113,f74])).
% 1.73/0.59  fof(f74,plain,(
% 1.73/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.73/0.59    inference(equality_resolution,[],[f59])).
% 1.73/0.59  fof(f59,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.73/0.59    inference(definition_unfolding,[],[f39,f54])).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,axiom,(
% 1.73/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.73/0.59    inference(cnf_transformation,[],[f9])).
% 1.73/0.59  fof(f9,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.73/0.59  fof(f113,plain,(
% 1.73/0.59    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f26,f29])).
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  fof(f71,plain,(
% 1.73/0.59    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 1.73/0.59    inference(equality_resolution,[],[f70])).
% 1.73/0.59  fof(f70,plain,(
% 1.73/0.59    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 1.73/0.59    inference(equality_resolution,[],[f57])).
% 1.73/0.59  fof(f57,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.73/0.59    inference(definition_unfolding,[],[f41,f54])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.73/0.59    inference(cnf_transformation,[],[f9])).
% 1.73/0.59  fof(f633,plain,(
% 1.73/0.59    ~spl6_2),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f608])).
% 1.73/0.59  fof(f608,plain,(
% 1.73/0.59    $false | ~spl6_2),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f35,f602,f30])).
% 1.73/0.59  fof(f602,plain,(
% 1.73/0.59    k1_xboole_0 != k3_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 1.73/0.59    inference(forward_demodulation,[],[f535,f104])).
% 1.73/0.59  fof(f535,plain,(
% 1.73/0.59    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl6_2),
% 1.73/0.59    inference(superposition,[],[f420,f52])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f6])).
% 1.73/0.59  fof(f6,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.73/0.59  fof(f420,plain,(
% 1.73/0.59    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl6_2),
% 1.73/0.59    inference(superposition,[],[f161,f412])).
% 1.73/0.59  fof(f412,plain,(
% 1.73/0.59    k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | ~spl6_2),
% 1.73/0.59    inference(avatar_component_clause,[],[f410])).
% 1.73/0.59  fof(f410,plain,(
% 1.73/0.59    spl6_2 <=> k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.73/0.59  fof(f161,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_enumset1(X0,X0,sK3),sK2)) )),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f87,f29])).
% 1.73/0.59  fof(f87,plain,(
% 1.73/0.59    ( ! [X0] : (~r1_xboole_0(k1_enumset1(X0,X0,sK3),sK2)) )),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f71,f24,f32])).
% 1.73/0.59  fof(f32,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f21])).
% 1.73/0.59  fof(f21,plain,(
% 1.73/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.73/0.59    inference(ennf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,plain,(
% 1.73/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.73/0.59    inference(rectify,[],[f5])).
% 1.73/0.59  fof(f5,axiom,(
% 1.73/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.73/0.59  fof(f24,plain,(
% 1.73/0.59    r2_hidden(sK3,sK2)),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f7])).
% 1.73/0.59  fof(f7,axiom,(
% 1.73/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.73/0.59  fof(f413,plain,(
% 1.73/0.59    spl6_1 | spl6_2),
% 1.73/0.59    inference(avatar_split_clause,[],[f115,f410,f406])).
% 1.73/0.59  fof(f115,plain,(
% 1.73/0.59    k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f114])).
% 1.73/0.59  fof(f114,plain,(
% 1.73/0.59    k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.73/0.59    inference(resolution,[],[f56,f69])).
% 1.73/0.59  fof(f69,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_enumset1(X0,X0,X0) = X3 | k1_enumset1(X1,X1,X1) = X3 | k1_enumset1(X2,X2,X2) = X3 | k1_enumset1(X0,X0,X1) = X3 | k1_enumset1(X1,X1,X2) = X3 | k1_enumset1(X0,X0,X2) = X3 | k1_enumset1(X0,X1,X2) = X3 | k1_xboole_0 = X3) )),
% 1.73/0.59    inference(definition_unfolding,[],[f42,f55,f55,f55,f54,f54,f54])).
% 1.73/0.59  fof(f55,plain,(
% 1.73/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f51,f54])).
% 1.73/0.59  fof(f51,plain,(
% 1.73/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f10])).
% 1.73/0.59  fof(f10,axiom,(
% 1.73/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X3 | k1_tarski(X0) = X3 | k1_tarski(X1) = X3 | k1_tarski(X2) = X3 | k2_tarski(X0,X1) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k1_enumset1(X0,X1,X2) = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  fof(f22,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.73/0.59    inference(ennf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.73/0.59  fof(f56,plain,(
% 1.73/0.59    r1_tarski(k3_xboole_0(sK0,sK1),k1_enumset1(sK3,sK3,sK3))),
% 1.73/0.59    inference(definition_unfolding,[],[f23,f55])).
% 1.73/0.59  fof(f23,plain,(
% 1.73/0.59    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  % SZS output end Proof for theBenchmark
% 1.73/0.59  % (29896)------------------------------
% 1.73/0.59  % (29896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (29896)Termination reason: Refutation
% 1.73/0.59  
% 1.73/0.59  % (29896)Memory used [KB]: 6652
% 1.73/0.59  % (29896)Time elapsed: 0.198 s
% 1.73/0.59  % (29896)------------------------------
% 1.73/0.59  % (29896)------------------------------
% 1.73/0.59  % (29887)Refutation not found, incomplete strategy% (29887)------------------------------
% 1.73/0.59  % (29887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (29887)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (29887)Memory used [KB]: 10618
% 1.73/0.59  % (29887)Time elapsed: 0.172 s
% 1.73/0.59  % (29887)------------------------------
% 1.73/0.59  % (29887)------------------------------
% 1.73/0.59  % (29870)Success in time 0.238 s
%------------------------------------------------------------------------------
