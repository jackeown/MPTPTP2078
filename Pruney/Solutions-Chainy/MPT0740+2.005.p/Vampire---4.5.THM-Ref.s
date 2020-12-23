%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:19 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 158 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  189 ( 369 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f504,f640,f933])).

fof(f933,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f931,f25])).

fof(f25,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f931,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f929,f44])).

fof(f44,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0))) ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f43,plain,(
    v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f929,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0)))
    | v3_ordinal1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f925,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f925,plain,
    ( r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f922,f44])).

fof(f922,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0)))
    | r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f888,f26])).

fof(f26,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f888,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k1_ordinal1(sK0),X3)
        | ~ v3_ordinal1(X3)
        | r2_hidden(k3_tarski(sK0),X3) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f887,f499])).

fof(f499,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl4_1
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f887,plain,(
    ! [X3] :
      ( ~ v3_ordinal1(X3)
      | ~ v1_ordinal1(k3_tarski(sK0))
      | ~ r2_hidden(k1_ordinal1(sK0),X3)
      | r2_hidden(k3_tarski(sK0),X3) ) ),
    inference(resolution,[],[f881,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v1_ordinal1(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(subsumption_resolution,[],[f27,f34])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f881,plain,(
    r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0)) ),
    inference(duplicate_literal_removal,[],[f876])).

fof(f876,plain,
    ( r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0))
    | r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0)) ),
    inference(resolution,[],[f851,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f851,plain,(
    ! [X4] :
      ( r1_tarski(sK2(sK0,X4),k1_ordinal1(sK0))
      | r1_tarski(k3_tarski(sK0),X4) ) ),
    inference(subsumption_resolution,[],[f849,f46])).

fof(f46,plain,(
    v1_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f849,plain,(
    ! [X4] :
      ( r1_tarski(k3_tarski(sK0),X4)
      | r1_tarski(sK2(sK0,X4),k1_ordinal1(sK0))
      | ~ v1_ordinal1(k1_ordinal1(sK0)) ) ),
    inference(resolution,[],[f579,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f579,plain,(
    ! [X17] :
      ( r2_hidden(sK2(sK0,X17),k1_ordinal1(sK0))
      | r1_tarski(k3_tarski(sK0),X17) ) ),
    inference(resolution,[],[f144,f159])).

fof(f159,plain,(
    r1_tarski(sK0,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f73,f46])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(k1_ordinal1(X0))
      | r1_tarski(X0,k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f31,f26])).

fof(f144,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,X6)
      | r2_hidden(sK2(X4,X5),X6)
      | r1_tarski(k3_tarski(X4),X5) ) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f640,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f634,f501,f497])).

fof(f501,plain,
    ( spl4_2
  <=> r2_hidden(sK1(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f634,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f629,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f629,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f154,f503])).

fof(f503,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f501])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f40,f93])).

fof(f93,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f504,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f491,f501,f497])).

fof(f491,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | v1_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f488,f143])).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r2_hidden(sK1(X2),X3)
      | v1_ordinal1(X2) ) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f488,plain,(
    r1_tarski(k3_tarski(sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f485])).

fof(f485,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | r1_tarski(k3_tarski(sK0),sK0) ),
    inference(resolution,[],[f481,f36])).

fof(f481,plain,(
    ! [X35] :
      ( r1_tarski(sK2(sK0,X35),sK0)
      | r1_tarski(k3_tarski(sK0),X35) ) ),
    inference(resolution,[],[f103,f41])).

fof(f41,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f29,f24])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | r1_tarski(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(resolution,[],[f35,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:11:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (29986)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (29976)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.48  % (29978)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (29975)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.48  % (29979)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (29974)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (29977)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.49  % (29988)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (29987)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (29982)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (29980)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  % (29994)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.50  % (29993)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.50  % (29985)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.50  % (29984)WARNING: option uwaf not known.
% 0.22/0.51  % (29990)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.51  % (29991)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.52  % (29992)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (29983)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (29989)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.52  % (29984)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.52  % (29981)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 1.29/0.53  % (29980)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f934,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(avatar_sat_refutation,[],[f504,f640,f933])).
% 1.29/0.53  fof(f933,plain,(
% 1.29/0.53    ~spl4_1),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f932])).
% 1.29/0.53  fof(f932,plain,(
% 1.29/0.53    $false | ~spl4_1),
% 1.29/0.53    inference(subsumption_resolution,[],[f931,f25])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ~v3_ordinal1(k3_tarski(sK0))),
% 1.29/0.53    inference(cnf_transformation,[],[f12])).
% 1.29/0.53  fof(f12,plain,(
% 1.29/0.53    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f11])).
% 1.29/0.53  fof(f11,negated_conjecture,(
% 1.29/0.53    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.29/0.53    inference(negated_conjecture,[],[f10])).
% 1.29/0.53  fof(f10,conjecture,(
% 1.29/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).
% 1.29/0.53  fof(f931,plain,(
% 1.29/0.53    v3_ordinal1(k3_tarski(sK0)) | ~spl4_1),
% 1.29/0.53    inference(subsumption_resolution,[],[f929,f44])).
% 1.29/0.53  fof(f44,plain,(
% 1.29/0.53    v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0)))),
% 1.29/0.53    inference(resolution,[],[f43,f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,axiom,(
% 1.29/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    v3_ordinal1(k1_ordinal1(sK0))),
% 1.29/0.53    inference(resolution,[],[f28,f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    v3_ordinal1(sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f12])).
% 1.29/0.53  fof(f929,plain,(
% 1.29/0.53    ~v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0))) | v3_ordinal1(k3_tarski(sK0)) | ~spl4_1),
% 1.29/0.53    inference(resolution,[],[f925,f34])).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | v3_ordinal1(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 1.29/0.53    inference(flattening,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,axiom,(
% 1.29/0.53    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 1.29/0.53  fof(f925,plain,(
% 1.29/0.53    r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0))) | ~spl4_1),
% 1.29/0.53    inference(subsumption_resolution,[],[f922,f44])).
% 1.29/0.53  fof(f922,plain,(
% 1.29/0.53    ~v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0))) | r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0))) | ~spl4_1),
% 1.29/0.53    inference(resolution,[],[f888,f26])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f6])).
% 1.29/0.53  fof(f6,axiom,(
% 1.29/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.29/0.53  fof(f888,plain,(
% 1.29/0.53    ( ! [X3] : (~r2_hidden(k1_ordinal1(sK0),X3) | ~v3_ordinal1(X3) | r2_hidden(k3_tarski(sK0),X3)) ) | ~spl4_1),
% 1.29/0.53    inference(subsumption_resolution,[],[f887,f499])).
% 1.29/0.53  fof(f499,plain,(
% 1.29/0.53    v1_ordinal1(k3_tarski(sK0)) | ~spl4_1),
% 1.29/0.53    inference(avatar_component_clause,[],[f497])).
% 1.29/0.53  fof(f497,plain,(
% 1.29/0.53    spl4_1 <=> v1_ordinal1(k3_tarski(sK0))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.29/0.53  fof(f887,plain,(
% 1.29/0.53    ( ! [X3] : (~v3_ordinal1(X3) | ~v1_ordinal1(k3_tarski(sK0)) | ~r2_hidden(k1_ordinal1(sK0),X3) | r2_hidden(k3_tarski(sK0),X3)) )),
% 1.29/0.53    inference(resolution,[],[f881,f184])).
% 1.29/0.53  fof(f184,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v3_ordinal1(X2) | ~v1_ordinal1(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f27,f34])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X2) | ~r1_tarski(X0,X1) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f14])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.29/0.53    inference(flattening,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,axiom,(
% 1.29/0.53    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).
% 1.29/0.53  fof(f881,plain,(
% 1.29/0.53    r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0))),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f876])).
% 1.29/0.53  fof(f876,plain,(
% 1.29/0.53    r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0)) | r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0))),
% 1.29/0.53    inference(resolution,[],[f851,f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.29/0.53  fof(f851,plain,(
% 1.29/0.53    ( ! [X4] : (r1_tarski(sK2(sK0,X4),k1_ordinal1(sK0)) | r1_tarski(k3_tarski(sK0),X4)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f849,f46])).
% 1.29/0.53  fof(f46,plain,(
% 1.29/0.53    v1_ordinal1(k1_ordinal1(sK0))),
% 1.29/0.53    inference(resolution,[],[f43,f29])).
% 1.29/0.53  fof(f29,plain,(
% 1.29/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f16])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.29/0.53  fof(f849,plain,(
% 1.29/0.53    ( ! [X4] : (r1_tarski(k3_tarski(sK0),X4) | r1_tarski(sK2(sK0,X4),k1_ordinal1(sK0)) | ~v1_ordinal1(k1_ordinal1(sK0))) )),
% 1.29/0.53    inference(resolution,[],[f579,f31])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.29/0.53  fof(f579,plain,(
% 1.29/0.53    ( ! [X17] : (r2_hidden(sK2(sK0,X17),k1_ordinal1(sK0)) | r1_tarski(k3_tarski(sK0),X17)) )),
% 1.29/0.53    inference(resolution,[],[f144,f159])).
% 1.29/0.53  fof(f159,plain,(
% 1.29/0.53    r1_tarski(sK0,k1_ordinal1(sK0))),
% 1.29/0.53    inference(resolution,[],[f73,f46])).
% 1.29/0.53  fof(f73,plain,(
% 1.29/0.53    ( ! [X0] : (~v1_ordinal1(k1_ordinal1(X0)) | r1_tarski(X0,k1_ordinal1(X0))) )),
% 1.29/0.53    inference(resolution,[],[f31,f26])).
% 1.29/0.53  fof(f144,plain,(
% 1.29/0.53    ( ! [X6,X4,X5] : (~r1_tarski(X4,X6) | r2_hidden(sK2(X4,X5),X6) | r1_tarski(k3_tarski(X4),X5)) )),
% 1.29/0.53    inference(resolution,[],[f37,f35])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f21])).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.53  fof(f640,plain,(
% 1.29/0.53    spl4_1 | ~spl4_2),
% 1.29/0.53    inference(avatar_split_clause,[],[f634,f501,f497])).
% 1.29/0.53  fof(f501,plain,(
% 1.29/0.53    spl4_2 <=> r2_hidden(sK1(k3_tarski(sK0)),sK0)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.29/0.53  fof(f634,plain,(
% 1.29/0.53    v1_ordinal1(k3_tarski(sK0)) | ~spl4_2),
% 1.29/0.53    inference(resolution,[],[f629,f33])).
% 1.29/0.53  fof(f33,plain,(
% 1.29/0.53    ( ! [X0] : (~r1_tarski(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f17])).
% 1.29/0.53  fof(f629,plain,(
% 1.29/0.53    r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl4_2),
% 1.29/0.53    inference(resolution,[],[f154,f503])).
% 1.29/0.53  fof(f503,plain,(
% 1.29/0.53    r2_hidden(sK1(k3_tarski(sK0)),sK0) | ~spl4_2),
% 1.29/0.53    inference(avatar_component_clause,[],[f501])).
% 1.29/0.53  fof(f154,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.29/0.53    inference(resolution,[],[f40,f93])).
% 1.29/0.53  fof(f93,plain,(
% 1.29/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f92])).
% 1.29/0.53  fof(f92,plain,(
% 1.29/0.53    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.29/0.53    inference(resolution,[],[f39,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f21])).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f21])).
% 1.29/0.53  fof(f40,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 1.29/0.53    inference(flattening,[],[f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 1.29/0.53    inference(ennf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 1.29/0.53  fof(f504,plain,(
% 1.29/0.53    spl4_1 | spl4_2),
% 1.29/0.53    inference(avatar_split_clause,[],[f491,f501,f497])).
% 1.29/0.53  fof(f491,plain,(
% 1.29/0.53    r2_hidden(sK1(k3_tarski(sK0)),sK0) | v1_ordinal1(k3_tarski(sK0))),
% 1.29/0.53    inference(resolution,[],[f488,f143])).
% 1.29/0.53  fof(f143,plain,(
% 1.29/0.53    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r2_hidden(sK1(X2),X3) | v1_ordinal1(X2)) )),
% 1.29/0.53    inference(resolution,[],[f37,f32])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f17])).
% 1.29/0.53  fof(f488,plain,(
% 1.29/0.53    r1_tarski(k3_tarski(sK0),sK0)),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f485])).
% 1.29/0.53  fof(f485,plain,(
% 1.29/0.53    r1_tarski(k3_tarski(sK0),sK0) | r1_tarski(k3_tarski(sK0),sK0)),
% 1.29/0.53    inference(resolution,[],[f481,f36])).
% 1.29/0.53  fof(f481,plain,(
% 1.29/0.53    ( ! [X35] : (r1_tarski(sK2(sK0,X35),sK0) | r1_tarski(k3_tarski(sK0),X35)) )),
% 1.29/0.53    inference(resolution,[],[f103,f41])).
% 1.29/0.53  fof(f41,plain,(
% 1.29/0.53    v1_ordinal1(sK0)),
% 1.29/0.53    inference(resolution,[],[f29,f24])).
% 1.29/0.53  fof(f103,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~v1_ordinal1(X0) | r1_tarski(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.29/0.53    inference(resolution,[],[f35,f31])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (29980)------------------------------
% 1.29/0.53  % (29980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (29980)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (29980)Memory used [KB]: 5628
% 1.29/0.53  % (29980)Time elapsed: 0.066 s
% 1.29/0.53  % (29980)------------------------------
% 1.29/0.53  % (29980)------------------------------
% 1.29/0.53  % (29973)Success in time 0.171 s
%------------------------------------------------------------------------------
