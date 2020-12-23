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
% DateTime   : Thu Dec  3 12:55:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 127 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 658 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f105,f123,f268,f281])).

fof(f281,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f275,f56,f75,f85])).

fof(f85,plain,
    ( spl4_9
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f75,plain,
    ( spl4_7
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f56,plain,
    ( spl4_3
  <=> v1_funct_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f275,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f58,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f268,plain,
    ( spl4_2
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl4_2
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f54,f157])).

fof(f157,plain,
    ( ! [X0] : v5_relat_1(k7_relat_1(sK1,X0),sK0)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f150,f115])).

fof(f115,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f87,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f87,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f150,plain,
    ( ! [X0] : v5_relat_1(k5_relat_1(k6_relat_1(X0),sK1),sK0)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f87,f82,f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k5_relat_1(X2,X1),X0)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k5_relat_1(X2,X1),X0)
        & v1_relat_1(k5_relat_1(X2,X1)) )
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k5_relat_1(X2,X1),X0)
        & v1_relat_1(k5_relat_1(X2,X1)) )
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v5_relat_1(k5_relat_1(X2,X1),X0)
        & v1_relat_1(k5_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc25_relat_1)).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f82,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f54,plain,
    ( ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_2
  <=> v5_relat_1(k7_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f123,plain,
    ( spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f122,f85,f75,f70,f65,f60])).

fof(f60,plain,
    ( spl4_4
  <=> v5_ordinal1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( spl4_5
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f70,plain,
    ( spl4_6
  <=> v5_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f122,plain,
    ( v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f67,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v5_ordinal1(k7_relat_1(X0,X1))
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v5_ordinal1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

fof(f67,plain,
    ( v3_ordinal1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f72,plain,
    ( v5_ordinal1(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f77,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f105,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f101,f48,f75,f85])).

fof(f48,plain,
    ( spl4_1
  <=> v1_relat_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

% (17380)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f25,f85])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
      | ~ v1_funct_1(k7_relat_1(sK1,sK2))
      | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
    & v3_ordinal1(sK2)
    & v5_ordinal1(sK1)
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
              | ~ v1_funct_1(k7_relat_1(X1,X2))
              | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
              | ~ v1_relat_1(k7_relat_1(X1,X2)) )
            & v3_ordinal1(X2) )
        & v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
            | ~ v1_funct_1(k7_relat_1(sK1,X2))
            | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
            | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(sK1)
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
          | ~ v1_funct_1(k7_relat_1(sK1,X2))
          | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
          | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
        & v3_ordinal1(X2) )
   => ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( v5_ordinal1(k7_relat_1(X1,X2))
              & v1_funct_1(k7_relat_1(X1,X2))
              & v5_relat_1(k7_relat_1(X1,X2),X0)
              & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( v5_ordinal1(k7_relat_1(X1,X2))
            & v1_funct_1(k7_relat_1(X1,X2))
            & v5_relat_1(k7_relat_1(X1,X2),X0)
            & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

fof(f83,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f80])).

fof(f26,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f75])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    v5_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f30,f60,f56,f52,f48])).

fof(f30,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:42 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.49  % (17387)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (17395)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.53  % (17383)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.53  % (17379)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.53  % (17384)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (17385)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (17391)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.54  % (17401)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.54  % (17398)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.54  % (17382)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (17388)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.54  % (17396)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.54  % (17393)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.54  % (17399)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.54  % (17400)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.54  % (17390)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.54  % (17386)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (17381)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.54  % (17386)Refutation not found, incomplete strategy% (17386)------------------------------
% 0.21/0.54  % (17386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17386)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17386)Memory used [KB]: 6140
% 0.21/0.54  % (17386)Time elapsed: 0.111 s
% 0.21/0.54  % (17386)------------------------------
% 0.21/0.54  % (17386)------------------------------
% 0.21/0.54  % (17385)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f105,f123,f268,f281])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    ~spl4_9 | ~spl4_7 | spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f275,f56,f75,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    spl4_9 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl4_7 <=> v1_funct_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl4_3 <=> v1_funct_1(k7_relat_1(sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.54    inference(resolution,[],[f58,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~v1_funct_1(k7_relat_1(sK1,sK2)) | spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f56])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    spl4_2 | ~spl4_8 | ~spl4_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f260])).
% 0.21/0.54  fof(f260,plain,(
% 0.21/0.54    $false | (spl4_2 | ~spl4_8 | ~spl4_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f54,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0] : (v5_relat_1(k7_relat_1(sK1,X0),sK0)) ) | (~spl4_8 | ~spl4_9)),
% 0.21/0.54    inference(forward_demodulation,[],[f150,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl4_9),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f87,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f85])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0] : (v5_relat_1(k5_relat_1(k6_relat_1(X0),sK1),sK0)) ) | (~spl4_8 | ~spl4_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f87,f82,f39,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v5_relat_1(k5_relat_1(X2,X1),X0) | ~v1_relat_1(X2) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(k5_relat_1(X2,X1),X0) & v1_relat_1(k5_relat_1(X2,X1))) | ~v1_relat_1(X2) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(k5_relat_1(X2,X1),X0) & v1_relat_1(k5_relat_1(X2,X1))) | (~v1_relat_1(X2) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_relat_1(X2) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v5_relat_1(k5_relat_1(X2,X1),X0) & v1_relat_1(k5_relat_1(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc25_relat_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    v5_relat_1(sK1,sK0) | ~spl4_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl4_8 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl4_2 <=> v5_relat_1(k7_relat_1(sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f122,f85,f75,f70,f65,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl4_4 <=> v5_ordinal1(k7_relat_1(sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl4_5 <=> v3_ordinal1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    spl4_6 <=> v5_ordinal1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    v5_ordinal1(k7_relat_1(sK1,sK2)) | (~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f87,f77,f72,f67,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v5_ordinal1(k7_relat_1(X0,X1)) | ~v3_ordinal1(X1) | ~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_ordinal1(k7_relat_1(X0,X1)) & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v3_ordinal1(X1) | ~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_ordinal1(k7_relat_1(X0,X1)) & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v3_ordinal1(X1) | ~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v5_ordinal1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v5_ordinal1(k7_relat_1(X0,X1)) & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    v3_ordinal1(sK2) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    v5_ordinal1(sK1) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f70])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    v1_funct_1(sK1) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ~spl4_9 | ~spl4_7 | spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f101,f48,f75,f85])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    spl4_1 <=> v1_relat_1(k7_relat_1(sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.54    inference(resolution,[],[f31,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~v1_relat_1(k7_relat_1(sK1,sK2)) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f48])).
% 0.21/0.54  % (17380)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f25,f85])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ((~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2))) & v3_ordinal1(sK2)) & v5_ordinal1(sK1) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(k7_relat_1(X1,X2)) | ~v1_funct_1(k7_relat_1(X1,X2)) | ~v5_relat_1(k7_relat_1(X1,X2),X0) | ~v1_relat_1(k7_relat_1(X1,X2))) & v3_ordinal1(X2)) & v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : ((~v5_ordinal1(k7_relat_1(sK1,X2)) | ~v1_funct_1(k7_relat_1(sK1,X2)) | ~v5_relat_1(k7_relat_1(sK1,X2),sK0) | ~v1_relat_1(k7_relat_1(sK1,X2))) & v3_ordinal1(X2)) & v5_ordinal1(sK1) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X2] : ((~v5_ordinal1(k7_relat_1(sK1,X2)) | ~v1_funct_1(k7_relat_1(sK1,X2)) | ~v5_relat_1(k7_relat_1(sK1,X2),sK0) | ~v1_relat_1(k7_relat_1(sK1,X2))) & v3_ordinal1(X2)) => ((~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2))) & v3_ordinal1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(k7_relat_1(X1,X2)) | ~v1_funct_1(k7_relat_1(X1,X2)) | ~v5_relat_1(k7_relat_1(X1,X2),X0) | ~v1_relat_1(k7_relat_1(X1,X2))) & v3_ordinal1(X2)) & v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(k7_relat_1(X1,X2)) | ~v1_funct_1(k7_relat_1(X1,X2)) | ~v5_relat_1(k7_relat_1(X1,X2),X0) | ~v1_relat_1(k7_relat_1(X1,X2))) & v3_ordinal1(X2)) & (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ((v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (v3_ordinal1(X2) => (v5_ordinal1(k7_relat_1(X1,X2)) & v1_funct_1(k7_relat_1(X1,X2)) & v5_relat_1(k7_relat_1(X1,X2),X0) & v1_relat_1(k7_relat_1(X1,X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0,X1] : ((v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (v3_ordinal1(X2) => (v5_ordinal1(k7_relat_1(X1,X2)) & v1_funct_1(k7_relat_1(X1,X2)) & v5_relat_1(k7_relat_1(X1,X2),X0) & v1_relat_1(k7_relat_1(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl4_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f26,f80])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    v5_relat_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f75])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    v1_funct_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f70])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v5_ordinal1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f65])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    v3_ordinal1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f60,f56,f52,f48])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ~v5_ordinal1(k7_relat_1(sK1,sK2)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v5_relat_1(k7_relat_1(sK1,sK2),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (17385)------------------------------
% 0.21/0.54  % (17385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17385)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (17385)Memory used [KB]: 10746
% 0.21/0.54  % (17385)Time elapsed: 0.106 s
% 0.21/0.54  % (17385)------------------------------
% 0.21/0.54  % (17385)------------------------------
% 0.21/0.55  % (17378)Success in time 0.182 s
%------------------------------------------------------------------------------
