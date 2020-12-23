%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  157 ( 265 expanded)
%              Number of equality atoms :   26 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f66,f74,f79,f105,f165,f182])).

fof(f182,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f168,f162,f51,f56,f41])).

fof(f41,plain,
    ( spl4_1
  <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f51,plain,
    ( spl4_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f162,plain,
    ( spl4_9
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f164,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f164,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f165,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f160,f102,f71,f56,f162])).

fof(f71,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f102,plain,
    ( spl4_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f110,f73])).

fof(f73,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK0,k1_relat_1(k7_relat_1(X0,sK1))) )
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f25])).

% (3606)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

% (3589)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f104,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( spl4_8
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f96,f76,f71,f102])).

fof(f76,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f96,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_6
    | spl4_7 ),
    inference(resolution,[],[f82,f78])).

fof(f78,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f82,plain,
    ( ! [X1] :
        ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),X1))
        | r2_hidden(sK0,X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f79,plain,
    ( ~ spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f68,f63,f76])).

fof(f63,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f74,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f67,f63,f71])).

fof(f67,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_5 ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f46,f63])).

fof(f46,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f61,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f19,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,
    ( r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f59,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f15,f56])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(f54,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f46])).

fof(f35,plain,(
    r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f17,f34])).

fof(f17,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (3593)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (3600)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (3610)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (3600)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (3586)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (3588)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (3584)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f66,f74,f79,f105,f165,f182])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    spl4_1 | ~spl4_4 | ~spl4_3 | ~spl4_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f168,f162,f51,f56,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    spl4_1 <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl4_4 <=> v1_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl4_3 <=> v1_funct_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    spl4_9 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) | ~spl4_9),
% 0.20/0.52    inference(resolution,[],[f164,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl4_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f162])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    spl4_9 | ~spl4_4 | ~spl4_6 | ~spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f160,f102,f71,f56,f162])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl4_6 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    spl4_8 <=> r2_hidden(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | (~spl4_6 | ~spl4_8)),
% 0.20/0.52    inference(resolution,[],[f110,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f71])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k1_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(sK0,k1_relat_1(k7_relat_1(X0,sK1)))) ) | ~spl4_8),
% 0.20/0.52    inference(resolution,[],[f104,f25])).
% 0.20/0.52  % (3606)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.52  % (3589)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1) | ~spl4_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f102])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl4_8 | ~spl4_6 | spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f96,f76,f71,f102])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl4_7 <=> r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1) | (~spl4_6 | spl4_7)),
% 0.20/0.52    inference(resolution,[],[f82,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f76])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),X1)) | r2_hidden(sK0,X1)) ) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f73,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ~spl4_7 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f68,f63,f76])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl4_5 <=> r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | ~spl4_5),
% 0.20/0.52    inference(resolution,[],[f65,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl4_6 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f67,f63,f71])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_5),
% 0.20/0.52    inference(resolution,[],[f65,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl4_5 | ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f61,f46,f63])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    spl4_2 <=> r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    r2_hidden(sK0,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1))) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f48,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f21,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f19,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f20,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f46])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f15,f56])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    v1_relat_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f16,f51])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f46])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_setfam_1(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 0.20/0.52    inference(definition_unfolding,[],[f17,f34])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f18,f41])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (3600)------------------------------
% 0.20/0.52  % (3600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3600)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (3600)Memory used [KB]: 10874
% 0.20/0.52  % (3600)Time elapsed: 0.125 s
% 0.20/0.52  % (3600)------------------------------
% 0.20/0.52  % (3600)------------------------------
% 0.20/0.52  % (3583)Success in time 0.169 s
%------------------------------------------------------------------------------
