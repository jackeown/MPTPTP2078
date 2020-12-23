%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  72 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  112 ( 184 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f152,f163,f179,f203])).

fof(f203,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f183,f156,f36,f26])).

fof(f26,plain,
    ( spl4_1
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f156,plain,
    ( spl4_11
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f183,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(superposition,[],[f59,f158])).

fof(f158,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f59,plain,
    ( ! [X2,X3] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))
    | ~ spl4_3 ),
    inference(superposition,[],[f15,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl4_3 ),
    inference(resolution,[],[f19,f38])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f179,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_10
    | spl4_12 ),
    inference(avatar_split_clause,[],[f178,f160,f145,f31,f156])).

fof(f31,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f145,plain,
    ( spl4_10
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f160,plain,
    ( spl4_12
  <=> r1_tarski(sK1,sK3(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f178,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK0,sK1)
    | sK1 = k2_xboole_0(sK0,sK1)
    | spl4_12 ),
    inference(resolution,[],[f162,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f162,plain,
    ( ~ r1_tarski(sK1,sK3(sK0,sK1,sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f154,f31,f160,f156])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,sK3(sK0,sK1,sK1))
    | sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f108,f23])).

fof(f23,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK1,sK3(sK0,sK1,X0))
        | sK1 = k2_xboole_0(sK0,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,sK3(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f152,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f23,f147])).

fof(f147,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f12,f36])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (987)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (997)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (997)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (990)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (980)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f29,f34,f39,f152,f163,f179,f203])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl4_1 | ~spl4_3 | ~spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f156,f36,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    spl4_1 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    spl4_3 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl4_11 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl4_3 | ~spl4_11)),
% 0.21/0.51    inference(superposition,[],[f59,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK0,sK1) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f156])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))) ) | ~spl4_3),
% 0.21/0.51    inference(superposition,[],[f15,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f19,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f36])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl4_11 | ~spl4_2 | ~spl4_10 | spl4_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f178,f160,f145,f31,f156])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl4_10 <=> r1_tarski(sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl4_12 <=> r1_tarski(sK1,sK3(sK0,sK1,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK0,sK1) | sK1 = k2_xboole_0(sK0,sK1) | spl4_12),
% 0.21/0.51    inference(resolution,[],[f162,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X2,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK3(sK0,sK1,sK1)) | spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl4_11 | ~spl4_12 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f154,f31,f160,f156])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK3(sK0,sK1,sK1)) | sK1 = k2_xboole_0(sK0,sK1) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f108,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK1,sK3(sK0,sK1,X0)) | sK1 = k2_xboole_0(sK0,X0)) ) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f22,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f31])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl4_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    $false | spl4_10),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f23,f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK1) | spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f12,f36])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f13,f31])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (997)------------------------------
% 0.21/0.51  % (997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (997)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (997)Memory used [KB]: 6396
% 0.21/0.51  % (997)Time elapsed: 0.083 s
% 0.21/0.51  % (997)------------------------------
% 0.21/0.51  % (997)------------------------------
% 0.21/0.51  % (1007)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (979)Success in time 0.153 s
%------------------------------------------------------------------------------
