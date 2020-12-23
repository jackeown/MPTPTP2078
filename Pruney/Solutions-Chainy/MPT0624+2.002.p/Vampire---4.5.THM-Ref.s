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
% DateTime   : Thu Dec  3 12:52:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 179 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 667 expanded)
%              Number of equality atoms :    7 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f39,f45,f53,f59,f69,f71,f73,f75])).

fof(f75,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f67,f38])).

fof(f38,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_4
  <=> r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( ~ r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_6
  <=> r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f63,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f62,f11])).

fof(f11,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( k1_funct_1(X1,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X1)) )
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( k1_funct_1(X1,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X1)) )
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(f62,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(sK2(X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f32,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f61,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(sK2(X0),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f60,f27])).

fof(f27,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl4_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(sK2(X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f16,f12])).

fof(f12,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,sK2(X2)) = X2
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f73,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f64,f52])).

fof(f64,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f38,f63])).

fof(f71,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f65,f38])).

fof(f65,plain,
    ( ~ r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f52,f63])).

fof(f69,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f38,f52,f63])).

fof(f59,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f54,f36,f56])).

fof(f56,plain,
    ( spl4_7
  <=> sK3(sK0,k2_relat_1(sK1)) = k1_funct_1(sK1,sK2(sK3(sK0,k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f54,plain,
    ( sK3(sK0,k2_relat_1(sK1)) = k1_funct_1(sK1,sK2(sK3(sK0,k2_relat_1(sK1))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f38,f12])).

fof(f53,plain,
    ( ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f46,f20,f50])).

fof(f20,plain,
    ( spl4_1
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,
    ( ~ r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f22,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f22,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f45,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f40,f36,f42])).

fof(f42,plain,
    ( spl4_5
  <=> r2_hidden(sK2(sK3(sK0,k2_relat_1(sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f40,plain,
    ( r2_hidden(sK2(sK3(sK0,k2_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f38,f11])).

fof(f39,plain,
    ( spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f34,f20,f36])).

fof(f34,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f22,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f30])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f20])).

fof(f15,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (23950)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (23941)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (23950)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f23,f28,f33,f39,f45,f53,f59,f69,f71,f73,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f67,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    spl4_4 <=> r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0) | (~spl4_2 | ~spl4_3 | spl4_6)),
% 0.21/0.54    inference(resolution,[],[f63,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) | spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    spl4_6 <=> r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f62,f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(sK2(X2),k1_relat_1(sK1)) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (? [X3] : (k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~r2_hidden(X2,X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f6])).
% 0.21/0.54  fof(f6,plain,(
% 0.21/0.54    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (? [X3] : (k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) | ~r2_hidden(X2,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : ~(! [X3] : ~(k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f3])).
% 0.21/0.54  fof(f3,conjecture,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : ~(! [X3] : ~(k1_funct_1(X1,X3) = X2 & r2_hidden(X3,k1_relat_1(X1))) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(sK2(X0),k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f61,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    spl4_3 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(sK2(X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f60,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    v1_funct_1(sK1) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    spl4_2 <=> v1_funct_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~r2_hidden(sK2(X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.54    inference(superposition,[],[f16,f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ( ! [X2] : (k1_funct_1(sK1,sK2(X2)) = X2 | ~r2_hidden(X2,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f64,f52])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f38,f63])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f65,f38])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0) | (~spl4_2 | ~spl4_3 | spl4_6)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f52,f63])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f38,f52,f63])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl4_7 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f36,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl4_7 <=> sK3(sK0,k2_relat_1(sK1)) = k1_funct_1(sK1,sK2(sK3(sK0,k2_relat_1(sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    sK3(sK0,k2_relat_1(sK1)) = k1_funct_1(sK1,sK2(sK3(sK0,k2_relat_1(sK1)))) | ~spl4_4),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f38,f12])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ~spl4_6 | spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f20,f50])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    spl4_1 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ~r2_hidden(sK3(sK0,k2_relat_1(sK1)),k2_relat_1(sK1)) | spl4_1),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f22,f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f20])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    spl4_5 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f40,f36,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    spl4_5 <=> r2_hidden(sK2(sK3(sK0,k2_relat_1(sK1))),k1_relat_1(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    r2_hidden(sK2(sK3(sK0,k2_relat_1(sK1))),k1_relat_1(sK1)) | ~spl4_4),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f38,f11])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    spl4_4 | spl4_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f34,f20,f36])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    r2_hidden(sK3(sK0,k2_relat_1(sK1)),sK0) | spl4_1),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f22,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    spl4_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f13,f30])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f14,f25])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    v1_funct_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ~spl4_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f15,f20])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (23950)------------------------------
% 0.21/0.55  % (23950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23950)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (23950)Memory used [KB]: 1663
% 0.21/0.55  % (23950)Time elapsed: 0.089 s
% 0.21/0.55  % (23950)------------------------------
% 0.21/0.55  % (23950)------------------------------
% 0.21/0.55  % (23927)Success in time 0.178 s
%------------------------------------------------------------------------------
