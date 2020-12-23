%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 (  96 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 ( 333 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f65,f70,f143])).

fof(f143,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f141,f64])).

fof(f64,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f141,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5 ),
    inference(subsumption_resolution,[],[f138,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f138,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(resolution,[],[f130,f104])).

fof(f104,plain,
    ( ! [X13] :
        ( r2_hidden(k4_tarski(X13,k1_funct_1(sK2,X13)),sK2)
        | ~ r2_hidden(X13,k1_relat_1(sK2)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f60,f46])).

fof(f46,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f60,plain,
    ( ! [X13] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X13,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X13,k1_funct_1(sK2,X13)),sK2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f41,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f130,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,k1_funct_1(sK2,sK0)),sK2)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(resolution,[],[f121,f21])).

fof(f21,plain,(
    ! [X4,X0,X3,X1] :
      ( sP5(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f121,plain,
    ( ! [X0] : ~ sP5(k1_funct_1(sK2,sK0),X0,sK1,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(resolution,[],[f120,f83])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),k7_relat_1(sK2,X2))
        | ~ sP5(X0,X1,X2,sK2) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ sP5(X0,X1,X2,sK2)
        | r2_hidden(k4_tarski(X1,X0),k7_relat_1(sK2,X2)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ sP5(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ sP5(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,
    ( ! [X4] : v1_relat_1(k7_relat_1(sK2,X4))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f55,f46])).

fof(f55,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(sK2)
        | v1_relat_1(k7_relat_1(sK2,X4)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f120,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_5 ),
    inference(resolution,[],[f79,f69])).

fof(f69,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_5
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f79,plain,
    ( ! [X19,X17,X18] :
        ( r2_hidden(X18,k2_relat_1(k7_relat_1(sK2,X19)))
        | ~ r2_hidden(k4_tarski(X17,X18),k7_relat_1(sK2,X19)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f72,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f70,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f20,f67])).

fof(f20,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

% (11424)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f65,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f18,f62])).

fof(f18,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (11414)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (11417)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (11414)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f42,f47,f52,f65,f70,f143])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f141,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl6_4 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k1_relat_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f138,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl6_3 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | (~spl6_1 | ~spl6_2 | spl6_5)),
% 0.22/0.50    inference(resolution,[],[f130,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X13] : (r2_hidden(k4_tarski(X13,k1_funct_1(sK2,X13)),sK2) | ~r2_hidden(X13,k1_relat_1(sK2))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f60,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    spl6_2 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X13] : (~v1_funct_1(sK2) | ~r2_hidden(X13,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X13,k1_funct_1(sK2,X13)),sK2)) ) | ~spl6_1),
% 0.22/0.50    inference(resolution,[],[f41,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    spl6_1 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(k4_tarski(X1,k1_funct_1(sK2,sK0)),sK2) | ~r2_hidden(X1,sK1)) ) | (~spl6_1 | ~spl6_2 | spl6_5)),
% 0.22/0.50    inference(resolution,[],[f121,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (sP5(X4,X3,X1,X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (~sP5(k1_funct_1(sK2,sK0),X0,sK1,sK2)) ) | (~spl6_1 | ~spl6_2 | spl6_5)),
% 0.22/0.50    inference(resolution,[],[f120,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X0),k7_relat_1(sK2,X2)) | ~sP5(X0,X1,X2,sK2)) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f73,f41])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(sK2) | ~sP5(X0,X1,X2,sK2) | r2_hidden(k4_tarski(X1,X0),k7_relat_1(sK2,X2))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.50    inference(resolution,[],[f72,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~sP5(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~sP5(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X4] : (v1_relat_1(k7_relat_1(sK2,X4))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f55,f46])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X4] : (~v1_funct_1(sK2) | v1_relat_1(k7_relat_1(sK2,X4))) ) | ~spl6_1),
% 0.22/0.50    inference(resolution,[],[f41,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))) ) | (~spl6_1 | ~spl6_2 | spl6_5)),
% 0.22/0.50    inference(resolution,[],[f79,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl6_5 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X19,X17,X18] : (r2_hidden(X18,k2_relat_1(k7_relat_1(sK2,X19))) | ~r2_hidden(k4_tarski(X17,X18),k7_relat_1(sK2,X19))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.50    inference(resolution,[],[f72,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f67])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f5])).
% 0.22/0.50  fof(f5,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).
% 0.22/0.51  % (11424)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f62])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f49])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    r2_hidden(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f44])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    v1_relat_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (11414)------------------------------
% 0.22/0.51  % (11414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11414)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (11414)Memory used [KB]: 10618
% 0.22/0.51  % (11414)Time elapsed: 0.077 s
% 0.22/0.51  % (11414)------------------------------
% 0.22/0.51  % (11414)------------------------------
% 0.22/0.51  % (11410)Success in time 0.149 s
%------------------------------------------------------------------------------
