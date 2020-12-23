%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 262 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f48,f52,f79,f136,f190,f200,f213])).

fof(f213,plain,
    ( spl9_3
    | ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl9_3
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f211,f47])).

fof(f47,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl9_3
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f211,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl9_15 ),
    inference(resolution,[],[f199,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f199,plain,
    ( sP4(sK0,sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl9_15
  <=> sP4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f200,plain,
    ( spl9_15
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f194,f188,f198])).

fof(f188,plain,
    ( spl9_14
  <=> r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK2),sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f194,plain,
    ( sP4(sK0,sK1)
    | ~ spl9_14 ),
    inference(resolution,[],[f189,f16])).

fof(f16,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f189,plain,
    ( r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK2),sK0),sK0),sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( spl9_14
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f145,f134,f188])).

fof(f134,plain,
    ( spl9_11
  <=> sP7(sK0,k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f145,plain,
    ( r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK2),sK0),sK0),sK1)
    | ~ spl9_11 ),
    inference(resolution,[],[f135,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(k4_tarski(sK8(X0,X1,X3),X3),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f135,plain,
    ( sP7(sK0,k2_relat_1(sK2),sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl9_11
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f120,f77,f50,f38,f134])).

fof(f38,plain,
    ( spl9_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f50,plain,
    ( spl9_4
  <=> r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f77,plain,
    ( spl9_7
  <=> k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f120,plain,
    ( sP7(sK0,k2_relat_1(sK2),sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f99,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k5_relat_1(sK2,sK1)))
        | sP7(X0,k2_relat_1(sK2),sK1) )
    | ~ spl9_2
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f98,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k5_relat_1(sK2,sK1)))
        | sP7(X0,k2_relat_1(sK2),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_7 ),
    inference(superposition,[],[f31,f78])).

fof(f78,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | sP7(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,
    ( spl9_7
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f61,f38,f34,f77])).

fof(f34,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f61,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f41,f39])).

fof(f41,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK2,X0)) = k9_relat_1(X0,k2_relat_1(sK2)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f35,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f52,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f12,f50])).

fof(f12,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(f48,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f13,f46])).

fof(f13,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f14,f38])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f11,f34])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (31892)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (31892)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (31897)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (31911)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f36,f40,f48,f52,f79,f136,f190,f200,f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl9_3 | ~spl9_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    $false | (spl9_3 | ~spl9_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl9_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl9_3 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl9_15),
% 0.21/0.48    inference(resolution,[],[f199,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~sP4(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP4(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    sP4(sK0,sK1) | ~spl9_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl9_15 <=> sP4(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    spl9_15 | ~spl9_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f194,f188,f198])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    spl9_14 <=> r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK2),sK0),sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    sP4(sK0,sK1) | ~spl9_14),
% 0.21/0.48    inference(resolution,[],[f189,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP4(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK2),sK0),sK0),sK1) | ~spl9_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f188])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl9_14 | ~spl9_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f145,f134,f188])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl9_11 <=> sP7(sK0,k2_relat_1(sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK8(sK1,k2_relat_1(sK2),sK0),sK0),sK1) | ~spl9_11),
% 0.21/0.48    inference(resolution,[],[f135,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(k4_tarski(sK8(X0,X1,X3),X3),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    sP7(sK0,k2_relat_1(sK2),sK1) | ~spl9_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f134])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl9_11 | ~spl9_2 | ~spl9_4 | ~spl9_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f77,f50,f38,f134])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl9_2 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl9_4 <=> r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl9_7 <=> k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    sP7(sK0,k2_relat_1(sK2),sK1) | (~spl9_2 | ~spl9_4 | ~spl9_7)),
% 0.21/0.48    inference(resolution,[],[f99,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) | ~spl9_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k5_relat_1(sK2,sK1))) | sP7(X0,k2_relat_1(sK2),sK1)) ) | (~spl9_2 | ~spl9_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl9_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k5_relat_1(sK2,sK1))) | sP7(X0,k2_relat_1(sK2),sK1) | ~v1_relat_1(sK1)) ) | ~spl9_7),
% 0.21/0.48    inference(superposition,[],[f31,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) | ~spl9_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | sP7(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl9_7 | ~spl9_1 | ~spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f38,f34,f77])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl9_1 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k2_relat_1(sK2)) | (~spl9_1 | ~spl9_2)),
% 0.21/0.48    inference(resolution,[],[f41,f39])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK2,X0)) = k9_relat_1(X0,k2_relat_1(sK2))) ) | ~spl9_1),
% 0.21/0.48    inference(resolution,[],[f35,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl9_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl9_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f50])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~spl9_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f46])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f38])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl9_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f34])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31892)------------------------------
% 0.21/0.48  % (31892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31892)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31892)Memory used [KB]: 6396
% 0.21/0.48  % (31892)Time elapsed: 0.064 s
% 0.21/0.48  % (31892)------------------------------
% 0.21/0.48  % (31892)------------------------------
% 0.21/0.48  % (31891)Success in time 0.123 s
%------------------------------------------------------------------------------
