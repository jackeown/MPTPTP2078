%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 171 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 ( 475 expanded)
%              Number of equality atoms :   27 (  93 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f49,f61,f76,f124,f176])).

fof(f176,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f144,f78])).

fof(f78,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f77,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f77,plain,
    ( sK1 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl8_2 ),
    inference(superposition,[],[f38,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f38,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl8_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f144,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(resolution,[],[f130,f129])).

fof(f129,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK4(X3)),sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl8_1
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f60,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f59])).

% (25682)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (25673)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (25686)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (25681)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (25672)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (25689)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (25669)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (25676)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (25678)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (25674)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (25671)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (25685)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (25684)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (25687)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f59,plain,
    ( spl8_6
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f130,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),X1)
        | k1_relat_1(sK2) = X1 )
    | ~ spl8_6 ),
    inference(resolution,[],[f60,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f124,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_5 ),
    inference(subsumption_resolution,[],[f122,f78])).

fof(f122,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl8_1
    | spl8_2
    | spl8_5 ),
    inference(subsumption_resolution,[],[f121,f120])).

fof(f120,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_2
    | spl8_5 ),
    inference(subsumption_resolution,[],[f118,f78])).

fof(f118,plain,
    ( r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k1_relat_1(sK2)
    | spl8_5 ),
    inference(factoring,[],[f94])).

fof(f94,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK1)
        | r2_hidden(sK5(sK2,X1),X1)
        | k1_relat_1(sK2) = X1 )
    | spl8_5 ),
    inference(resolution,[],[f89,f23])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X0,sK1) )
    | spl8_5 ),
    inference(resolution,[],[f88,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f88,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK1,sK0))
        | ~ r2_hidden(X0,sK2) )
    | spl8_5 ),
    inference(subsumption_resolution,[],[f87,f57])).

fof(f57,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_5
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK0))
      | r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f52,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k2_zfmisc_1(sK1,sK0))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f121,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k1_relat_1(sK2)
    | ~ spl8_1
    | spl8_2
    | spl8_5 ),
    inference(resolution,[],[f120,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,X0),sK1)
        | ~ r2_hidden(sK5(sK2,X0),X0)
        | k1_relat_1(sK2) = X0 )
    | ~ spl8_1 ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f74,f48])).

fof(f48,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl8_4
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f74,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f50,f73])).

fof(f73,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f71,f19])).

fof(f71,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_2 ),
    inference(superposition,[],[f39,f25])).

fof(f39,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f50,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl8_3
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f61,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f51,f59,f55])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f19,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f49,plain,
    ( spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f16,f37,f46])).

fof(f16,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f17,f37,f42])).

fof(f17,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f18,f37,f34])).

fof(f18,plain,(
    ! [X3] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (25675)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (25680)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (25670)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (25680)Refutation not found, incomplete strategy% (25680)------------------------------
% 0.21/0.47  % (25680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (25680)Memory used [KB]: 10618
% 0.21/0.47  % (25680)Time elapsed: 0.004 s
% 0.21/0.47  % (25680)------------------------------
% 0.21/0.47  % (25680)------------------------------
% 0.21/0.47  % (25670)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f40,f44,f49,f61,f76,f124,f176])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ~spl8_1 | spl8_2 | ~spl8_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    $false | (~spl8_1 | spl8_2 | ~spl8_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f144,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    sK1 != k1_relat_1(sK2) | spl8_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f77,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    sK1 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl8_2),
% 0.21/0.47    inference(superposition,[],[f38,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    sK1 != k1_relset_1(sK1,sK0,sK2) | spl8_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl8_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    sK1 = k1_relat_1(sK2) | (~spl8_1 | ~spl8_6)),
% 0.21/0.47    inference(resolution,[],[f130,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl8_1 | ~spl8_6)),
% 0.21/0.47    inference(resolution,[],[f60,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK4(X3)),sK2) | ~r2_hidden(X3,sK1)) ) | ~spl8_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl8_1 <=> ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl8_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  % (25682)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (25673)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (25686)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (25681)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (25672)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (25689)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (25669)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (25676)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (25678)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (25674)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (25671)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (25685)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (25684)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (25687)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl8_6 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(sK5(sK2,X1),X1) | k1_relat_1(sK2) = X1) ) | ~spl8_6),
% 0.21/0.49    inference(resolution,[],[f60,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl8_1 | spl8_2 | spl8_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    $false | (~spl8_1 | spl8_2 | spl8_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f78])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK2) | (~spl8_1 | spl8_2 | spl8_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK1),sK1) | (spl8_2 | spl8_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f78])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k1_relat_1(sK2) | spl8_5),
% 0.21/0.49    inference(factoring,[],[f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK1) | r2_hidden(sK5(sK2,X1),X1) | k1_relat_1(sK2) = X1) ) | spl8_5),
% 0.21/0.49    inference(resolution,[],[f89,f23])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,sK1)) ) | spl8_5),
% 0.21/0.49    inference(resolution,[],[f88,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) | ~r2_hidden(X0,sK2)) ) | spl8_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_zfmisc_1(sK1,sK0)) | spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl8_5 <=> v1_xboole_0(k2_zfmisc_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | v1_xboole_0(k2_zfmisc_1(sK1,sK0)) | r2_hidden(X0,k2_zfmisc_1(sK1,sK0))) )),
% 0.21/0.50    inference(resolution,[],[f52,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(X1,k2_zfmisc_1(sK1,sK0)) | ~r2_hidden(X1,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f19,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK2,sK1),sK1) | sK1 = k1_relat_1(sK2) | (~spl8_1 | spl8_2 | spl8_5)),
% 0.21/0.50    inference(resolution,[],[f120,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5(sK2,X0),sK1) | ~r2_hidden(sK5(sK2,X0),X0) | k1_relat_1(sK2) = X0) ) | ~spl8_1),
% 0.21/0.50    inference(resolution,[],[f35,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    $false | (~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    r2_hidden(sK3,sK1) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl8_4 <=> r2_hidden(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~r2_hidden(sK3,sK1) | (~spl8_2 | ~spl8_3)),
% 0.21/0.50    inference(backward_demodulation,[],[f50,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    sK1 = k1_relat_1(sK2) | ~spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f71,f19])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    sK1 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl8_2),
% 0.21/0.50    inference(superposition,[],[f39,f25])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    sK1 = k1_relset_1(sK1,sK0,sK2) | ~spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f37])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl8_3),
% 0.21/0.50    inference(resolution,[],[f43,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) ) | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl8_3 <=> ! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~spl8_5 | spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f59,f55])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK1,sK0))) )),
% 0.21/0.50    inference(resolution,[],[f19,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl8_4 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f37,f46])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl8_3 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f37,f42])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl8_1 | spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f37,f34])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X3] : (sK1 = k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (25670)------------------------------
% 0.21/0.50  % (25670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25670)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (25670)Memory used [KB]: 10618
% 0.21/0.50  % (25670)Time elapsed: 0.057 s
% 0.21/0.50  % (25670)------------------------------
% 0.21/0.50  % (25670)------------------------------
% 0.21/0.50  % (25668)Success in time 0.143 s
%------------------------------------------------------------------------------
