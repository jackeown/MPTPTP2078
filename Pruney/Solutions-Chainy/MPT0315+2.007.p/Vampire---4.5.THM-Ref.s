%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 156 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 312 expanded)
%              Number of equality atoms :   57 ( 130 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f382,f541])).

fof(f541,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f527])).

fof(f527,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | ~ spl4_1 ),
    inference(superposition,[],[f54,f507])).

fof(f507,plain,
    ( ! [X12,X13] : k2_zfmisc_1(sK0,X12) = k4_xboole_0(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK1,X13))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f487,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f53,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f487,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK1,X13))
        | k2_zfmisc_1(sK0,X12) = k4_xboole_0(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK1,X13)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f90,f424])).

fof(f424,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f423,f38])).

fof(f38,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f423,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f411,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f34,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f411,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k4_xboole_0(sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl4_1 ),
    inference(superposition,[],[f36,f404])).

fof(f404,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f27])).

fof(f42,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f33,f25,f25,f25])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f90,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X3,k4_xboole_0(X3,X4)) != k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f64,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f54,plain,(
    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f28,f21])).

fof(f21,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & ( r1_xboole_0(sK2,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & ( r1_xboole_0(sK2,sK3)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f382,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f336,f58])).

fof(f336,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k1_xboole_0)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f158,f235])).

fof(f235,plain,
    ( ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X9,sK2),k4_xboole_0(k2_zfmisc_1(X9,sK2),k2_zfmisc_1(X10,sK3)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f234,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f234,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_zfmisc_1(X9,sK2),k4_xboole_0(k2_zfmisc_1(X9,sK2),k2_zfmisc_1(X10,sK3))) = k2_zfmisc_1(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f208,f50])).

fof(f208,plain,
    ( ! [X10,X9] : k4_xboole_0(k2_zfmisc_1(X9,sK2),k4_xboole_0(k2_zfmisc_1(X9,sK2),k2_zfmisc_1(X10,sK3))) = k2_zfmisc_1(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(sK2,sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,
    ( sK2 = k4_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f27,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_2
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f158,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))) != k4_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))) ),
    inference(resolution,[],[f147,f28])).

fof(f147,plain,(
    ~ r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))) ),
    inference(resolution,[],[f71,f26])).

fof(f71,plain,(
    ~ r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    inference(resolution,[],[f67,f35])).

fof(f67,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    inference(resolution,[],[f61,f26])).

fof(f61,plain,(
    ~ r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f35,f21])).

fof(f47,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f20,f44,f40])).

fof(f20,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (19217)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (19215)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (19222)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (19217)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (19214)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (19242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (19216)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (19225)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (19228)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (19219)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (19238)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f553,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f47,f382,f541])).
% 0.20/0.52  fof(f541,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f540])).
% 0.20/0.52  fof(f540,plain,(
% 0.20/0.52    $false | ~spl4_1),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f527])).
% 0.20/0.52  fof(f527,plain,(
% 0.20/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f54,f507])).
% 0.20/0.52  fof(f507,plain,(
% 0.20/0.52    ( ! [X12,X13] : (k2_zfmisc_1(sK0,X12) = k4_xboole_0(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK1,X13))) ) | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f487,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f53,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r1_xboole_0(X2,X1) | k4_xboole_0(X1,X2) = X1) )),
% 0.20/0.52    inference(resolution,[],[f27,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.52  fof(f487,plain,(
% 0.20/0.52    ( ! [X12,X13] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK1,X13)) | k2_zfmisc_1(sK0,X12) = k4_xboole_0(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK1,X13))) ) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f90,f424])).
% 0.20/0.52  fof(f424,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)))) ) | ~spl4_1),
% 0.20/0.52    inference(forward_demodulation,[],[f423,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl4_1),
% 0.20/0.52    inference(forward_demodulation,[],[f411,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f34,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.52  fof(f411,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k4_xboole_0(sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f36,f404])).
% 0.20/0.52  fof(f404,plain,(
% 0.20/0.52    sK0 = k4_xboole_0(sK0,sK1) | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f42,f27])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f25,f25,f25])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) != k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4) | k4_xboole_0(X3,X4) = X3) )),
% 0.20/0.52    inference(resolution,[],[f64,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) | k4_xboole_0(X2,X3) = X2) )),
% 0.20/0.52    inference(resolution,[],[f35,f27])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f25])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.52    inference(resolution,[],[f28,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1))) => (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.52  fof(f382,plain,(
% 0.20/0.52    ~spl4_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f381])).
% 0.20/0.52  fof(f381,plain,(
% 0.20/0.52    $false | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f336,f58])).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k1_xboole_0))) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f158,f235])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X9,sK2),k4_xboole_0(k2_zfmisc_1(X9,sK2),k2_zfmisc_1(X10,sK3)))) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f234,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ( ! [X10,X9] : (k4_xboole_0(k2_zfmisc_1(X9,sK2),k4_xboole_0(k2_zfmisc_1(X9,sK2),k2_zfmisc_1(X10,sK3))) = k2_zfmisc_1(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f208,f50])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    ( ! [X10,X9] : (k4_xboole_0(k2_zfmisc_1(X9,sK2),k4_xboole_0(k2_zfmisc_1(X9,sK2),k2_zfmisc_1(X10,sK3))) = k2_zfmisc_1(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(sK2,sK2))) ) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f36,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    sK2 = k4_xboole_0(sK2,sK3) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f27,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    r1_xboole_0(sK2,sK3) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    spl4_2 <=> r1_xboole_0(sK2,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))) != k4_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))))),
% 0.20/0.52    inference(resolution,[],[f147,f28])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ~r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))))),
% 0.20/0.52    inference(resolution,[],[f71,f26])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ~r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 0.20/0.52    inference(resolution,[],[f67,f35])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~r1_xboole_0(k2_zfmisc_1(sK1,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 0.20/0.52    inference(resolution,[],[f61,f26])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ~r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),k2_zfmisc_1(sK1,sK3))),
% 0.20/0.52    inference(resolution,[],[f35,f21])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl4_1 | spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f20,f44,f40])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (19217)------------------------------
% 0.20/0.52  % (19217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19217)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (19217)Memory used [KB]: 11129
% 0.20/0.52  % (19217)Time elapsed: 0.123 s
% 0.20/0.52  % (19217)------------------------------
% 0.20/0.52  % (19217)------------------------------
% 0.20/0.52  % (19224)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (19209)Success in time 0.166 s
%------------------------------------------------------------------------------
