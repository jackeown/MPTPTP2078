%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  62 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 193 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f60,f62])).

fof(f62,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f61,f57,f50,f35])).

fof(f35,plain,
    ( spl3_1
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_5
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f61,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f59,f54])).

fof(f54,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,
    ( ~ spl3_4
    | ~ spl3_3
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f55,f40,f57,f45,f50])).

fof(f45,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( spl3_2
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f42,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f35])).

fof(f23,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (18898)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.45  % (18898)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f60,f62])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl3_1 | ~spl3_4 | ~spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f61,f57,f50,f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    spl3_1 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl3_5 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | (~spl3_4 | ~spl3_5)),
% 0.22/0.45    inference(forward_demodulation,[],[f59,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_4),
% 0.22/0.45    inference(resolution,[],[f52,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f50])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f57])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ~spl3_4 | ~spl3_3 | spl3_5 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f55,f40,f57,f45,f50])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl3_3 <=> v1_funct_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl3_2 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.22/0.45    inference(resolution,[],[f42,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f40])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    spl3_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.45    inference(negated_conjecture,[],[f11])).
% 0.22/0.45  fof(f11,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f45])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v1_funct_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f40])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f35])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (18898)------------------------------
% 0.22/0.45  % (18898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (18898)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (18898)Memory used [KB]: 10618
% 0.22/0.45  % (18898)Time elapsed: 0.005 s
% 0.22/0.45  % (18898)------------------------------
% 0.22/0.45  % (18898)------------------------------
% 0.22/0.45  % (18886)Success in time 0.093 s
%------------------------------------------------------------------------------
