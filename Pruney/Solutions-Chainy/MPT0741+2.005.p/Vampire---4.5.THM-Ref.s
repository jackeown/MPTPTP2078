%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 141 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 457 expanded)
%              Number of equality atoms :    9 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f40,f51,f56,f59,f64,f69,f74,f94,f97])).

fof(f97,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f49,plain,
    ( ~ v2_ordinal1(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_4
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f46,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_3
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f93,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | v2_ordinal1(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f63])).

fof(f63,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(sK3(X4))
      | ~ v3_ordinal1(sK2(X4))
      | v2_ordinal1(X4) ) ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f26,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f90,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(sK2(X4))
      | sK3(X4) = sK2(X4)
      | ~ v3_ordinal1(sK3(X4))
      | v2_ordinal1(X4) ) ),
    inference(subsumption_resolution,[],[f81,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X4] :
      ( r2_hidden(sK3(X4),sK2(X4))
      | ~ v3_ordinal1(sK2(X4))
      | sK3(X4) = sK2(X4)
      | ~ v3_ordinal1(sK3(X4))
      | v2_ordinal1(X4) ) ),
    inference(resolution,[],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f94,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f49,f46,f63,f91])).

fof(f74,plain,
    ( spl4_7
    | spl4_4 ),
    inference(avatar_split_clause,[],[f52,f48,f71])).

fof(f71,plain,
    ( spl4_7
  <=> r1_tarski(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f52,plain,
    ( v2_ordinal1(sK0)
    | r1_tarski(sK3(sK0),sK0) ),
    inference(resolution,[],[f24,f15])).

fof(f15,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f41,f48,f66])).

fof(f66,plain,
    ( spl4_6
  <=> r1_tarski(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f41,plain,
    ( v2_ordinal1(sK0)
    | r1_tarski(sK2(sK0),sK0) ),
    inference(resolution,[],[f23,f15])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,
    ( spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f53,f48,f61])).

fof(f53,plain,
    ( v2_ordinal1(sK0)
    | v3_ordinal1(sK3(sK0)) ),
    inference(resolution,[],[f24,f14])).

fof(f14,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f55,f39])).

fof(f39,plain,
    ( v1_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_2
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f55,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f50,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(f50,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f56,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f31,f39,f50,f18])).

fof(f51,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f42,f48,f44])).

fof(f42,plain,
    ( v2_ordinal1(sK0)
    | v3_ordinal1(sK2(sK0)) ),
    inference(resolution,[],[f23,f14])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f37])).

fof(f35,plain,(
    v1_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f33,plain,
    ( v1_ordinal1(sK0)
    | r1_tarski(sK1(sK0),sK0) ),
    inference(resolution,[],[f20,f15])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:43:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (7706)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (7706)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f32,f40,f51,f56,f59,f64,f69,f74,f94,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~spl4_3 | spl4_4 | ~spl4_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    $false | (~spl4_3 | spl4_4 | ~spl4_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f95,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ~v2_ordinal1(sK0) | spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl4_4 <=> v2_ordinal1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    v2_ordinal1(sK0) | (~spl4_3 | ~spl4_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f93,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    v3_ordinal1(sK2(sK0)) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_3 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ~v3_ordinal1(sK2(sK0)) | v2_ordinal1(sK0) | ~spl4_5),
% 0.21/0.46    inference(resolution,[],[f91,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    v3_ordinal1(sK3(sK0)) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_5 <=> v3_ordinal1(sK3(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X4] : (~v3_ordinal1(sK3(X4)) | ~v3_ordinal1(sK2(X4)) | v2_ordinal1(X4)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f90,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0] : (sK2(X0) != sK3(X0) | v2_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X4] : (~v3_ordinal1(sK2(X4)) | sK3(X4) = sK2(X4) | ~v3_ordinal1(sK3(X4)) | v2_ordinal1(X4)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f81,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK3(X0),sK2(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X4] : (r2_hidden(sK3(X4),sK2(X4)) | ~v3_ordinal1(sK2(X4)) | sK3(X4) = sK2(X4) | ~v3_ordinal1(sK3(X4)) | v2_ordinal1(X4)) )),
% 0.21/0.46    inference(resolution,[],[f17,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK2(X0),sK3(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | X0 = X1 | ~v3_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ~spl4_3 | spl4_4 | ~spl4_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    $false | (~spl4_3 | spl4_4 | ~spl4_5)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f49,f46,f63,f91])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl4_7 | spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f52,f48,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl4_7 <=> r1_tarski(sK3(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    v2_ordinal1(sK0) | r1_tarski(sK3(sK0),sK0)),
% 0.21/0.46    inference(resolution,[],[f24,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,sK0) | r1_tarski(X1,sK0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v2_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl4_6 | spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f48,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl4_6 <=> r1_tarski(sK2(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v2_ordinal1(sK0) | r1_tarski(sK2(sK0),sK0)),
% 0.21/0.46    inference(resolution,[],[f23,f15])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v2_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl4_5 | spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f53,f48,f61])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    v2_ordinal1(sK0) | v3_ordinal1(sK3(sK0))),
% 0.21/0.46    inference(resolution,[],[f24,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f57,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ~v3_ordinal1(sK0) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl4_1 <=> v3_ordinal1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    v3_ordinal1(sK0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f55,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    v1_ordinal1(sK0) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl4_2 <=> v1_ordinal1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ~v1_ordinal1(sK0) | v3_ordinal1(sK0) | ~spl4_4),
% 0.21/0.46    inference(resolution,[],[f50,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_ordinal1(X0) | ~v1_ordinal1(X0) | v3_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) => v3_ordinal1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    v2_ordinal1(sK0) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f31,f39,f50,f18])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl4_3 | spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f42,f48,f44])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    v2_ordinal1(sK0) | v3_ordinal1(sK2(sK0))),
% 0.21/0.46    inference(resolution,[],[f23,f14])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f37])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    v1_ordinal1(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f33,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_ordinal1(sK0) | r1_tarski(sK1(sK0),sK0)),
% 0.21/0.46    inference(resolution,[],[f20,f15])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f29])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ~v3_ordinal1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7706)------------------------------
% 0.21/0.46  % (7706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7706)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7706)Memory used [KB]: 6140
% 0.21/0.47  % (7706)Time elapsed: 0.060 s
% 0.21/0.47  % (7706)------------------------------
% 0.21/0.47  % (7706)------------------------------
% 0.21/0.47  % (7697)Success in time 0.114 s
%------------------------------------------------------------------------------
