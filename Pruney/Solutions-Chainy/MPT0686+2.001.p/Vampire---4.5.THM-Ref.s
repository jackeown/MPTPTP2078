%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  73 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 231 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f60,f79])).

% (9692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (9706)Refutation not found, incomplete strategy% (9706)------------------------------
% (9706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9706)Termination reason: Refutation not found, incomplete strategy

% (9706)Memory used [KB]: 10490
% (9706)Time elapsed: 0.120 s
% (9706)------------------------------
% (9706)------------------------------
% (9701)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f79,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f76,f59])).

fof(f59,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_4
  <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f76,plain,
    ( r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f67,f64])).

% (9698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f64,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,
    ( ! [X0,X1] : ~ sP4(X0,k3_xboole_0(sK1,sK2),X1)
    | ~ spl6_3 ),
    inference(resolution,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f55,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
    | ~ spl6_3 ),
    inference(resolution,[],[f43,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f43,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl6_3
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f52,plain,
    ( ! [X4,X5] :
        ( sP4(X4,X5,sK0)
        | ~ r2_hidden(X4,k10_relat_1(sK0,X5)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f47,f33])).

fof(f33,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl6_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f47,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK0)
        | sP4(X4,X5,sK0)
        | ~ r2_hidden(X4,k10_relat_1(sK0,X5)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl6_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

% (9698)Refutation not found, incomplete strategy% (9698)------------------------------
% (9698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f67,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1)))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f26,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f45,f33])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f38,f27])).

% (9705)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

% (9698)Termination reason: Refutation not found, incomplete strategy

% (9698)Memory used [KB]: 6012
% (9698)Time elapsed: 0.002 s
% (9698)------------------------------
% (9698)------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f15,f57])).

fof(f15,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

fof(f44,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f14,f41])).

fof(f14,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (9694)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (9687)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (9687)Refutation not found, incomplete strategy% (9687)------------------------------
% 0.22/0.50  % (9687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9687)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (9687)Memory used [KB]: 10490
% 0.22/0.50  % (9687)Time elapsed: 0.101 s
% 0.22/0.50  % (9687)------------------------------
% 0.22/0.50  % (9687)------------------------------
% 0.22/0.51  % (9704)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (9691)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (9689)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (9690)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (9700)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (9689)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (9706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f34,f39,f44,f60,f79])).
% 0.22/0.52  % (9692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (9706)Refutation not found, incomplete strategy% (9706)------------------------------
% 0.22/0.52  % (9706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9706)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9706)Memory used [KB]: 10490
% 0.22/0.52  % (9706)Time elapsed: 0.120 s
% 0.22/0.52  % (9706)------------------------------
% 0.22/0.52  % (9706)------------------------------
% 0.22/0.52  % (9701)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f76,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl6_4 <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.52    inference(resolution,[],[f67,f64])).
% 0.22/0.52  % (9698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,k3_xboole_0(sK1,sK2)))) ) | (~spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.52    inference(resolution,[],[f52,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP4(X0,k3_xboole_0(sK1,sK2),X1)) ) | ~spl6_3),
% 0.22/0.52    inference(resolution,[],[f55,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(k1_funct_1(X0,X3),X1) | ~sP4(X3,X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) ) | ~spl6_3),
% 0.22/0.52    inference(resolution,[],[f43,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    r1_xboole_0(sK1,sK2) | ~spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    spl6_3 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X4,X5] : (sP4(X4,X5,sK0) | ~r2_hidden(X4,k10_relat_1(sK0,X5))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f47,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    spl6_1 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~v1_relat_1(sK0) | sP4(X4,X5,sK0) | ~r2_hidden(X4,k10_relat_1(sK0,X5))) ) | ~spl6_2),
% 0.22/0.52    inference(resolution,[],[f38,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP4(X3,X1,X0) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    v1_funct_1(sK0) | ~spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    spl6_2 <=> v1_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  % (9698)Refutation not found, incomplete strategy% (9698)------------------------------
% 0.22/0.52  % (9698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK5(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1))) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.52    inference(superposition,[],[f26,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f45,f33])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(sK0) | k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl6_2),
% 0.22/0.52    inference(resolution,[],[f38,f27])).
% 0.22/0.52  % (9705)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  % (9698)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9698)Memory used [KB]: 6012
% 0.22/0.52  % (9698)Time elapsed: 0.002 s
% 0.22/0.52  % (9698)------------------------------
% 0.22/0.52  % (9698)------------------------------
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f15,f57])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f4])).
% 0.22/0.52  fof(f4,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f14,f41])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    r1_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f16,f31])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (9689)------------------------------
% 0.22/0.52  % (9689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9689)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (9689)Memory used [KB]: 10618
% 0.22/0.52  % (9689)Time elapsed: 0.095 s
% 0.22/0.52  % (9689)------------------------------
% 0.22/0.52  % (9689)------------------------------
% 0.22/0.52  % (9685)Success in time 0.167 s
%------------------------------------------------------------------------------
