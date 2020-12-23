%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:30 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 134 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 334 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f71,f89,f94,f124])).

fof(f124,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f34,f49,f113,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f113,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f106,f52])).

fof(f52,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl9_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f106,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f70,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f70,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl9_3
  <=> ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f49,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl9_1
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f94,plain,
    ( spl9_2
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl9_2
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f66,f75,f88])).

fof(f88,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK4(X3),X3),sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_4
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f75,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK8(sK1,k2_relat_1(sK2))),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f67,f32])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,
    ( ~ r2_hidden(sK8(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f62,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f53,f58,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f36,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f16,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f35,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f53,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f66,plain,
    ( r2_hidden(sK8(sK1,k2_relat_1(sK2)),sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f62,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f43,f51,f87])).

fof(f43,plain,(
    ! [X3] :
      ( sK1 = k2_relat_1(sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    inference(backward_demodulation,[],[f15,f36])).

fof(f15,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(sK4(X3),X3),sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f42,f51,f69])).

fof(f42,plain,(
    ! [X4] :
      ( sK1 != k2_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(backward_demodulation,[],[f14,f36])).

fof(f14,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f41,f51,f47])).

fof(f41,plain,
    ( sK1 != k2_relat_1(sK2)
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f13,f36])).

fof(f13,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (30319)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (30323)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.19/0.51  % (30310)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.19/0.51  % (30311)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.51  % (30336)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.19/0.52  % (30315)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.52  % (30314)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.52  % (30307)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.52  % (30329)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.53  % (30320)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.53  % (30312)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.53  % (30322)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.53  % (30316)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.53  % (30310)Refutation found. Thanks to Tanya!
% 1.33/0.53  % SZS status Theorem for theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f125,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(avatar_sat_refutation,[],[f54,f71,f89,f94,f124])).
% 1.33/0.53  fof(f124,plain,(
% 1.33/0.53    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 1.33/0.53    inference(avatar_contradiction_clause,[],[f119])).
% 1.33/0.53  fof(f119,plain,(
% 1.33/0.53    $false | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f34,f49,f113,f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f12])).
% 1.33/0.53  fof(f12,plain,(
% 1.33/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.53  fof(f113,plain,(
% 1.33/0.53    ~r2_hidden(sK3,sK1) | (~spl9_2 | ~spl9_3)),
% 1.33/0.53    inference(forward_demodulation,[],[f106,f52])).
% 1.33/0.53  fof(f52,plain,(
% 1.33/0.53    sK1 = k2_relat_1(sK2) | ~spl9_2),
% 1.33/0.53    inference(avatar_component_clause,[],[f51])).
% 1.33/0.53  fof(f51,plain,(
% 1.33/0.53    spl9_2 <=> sK1 = k2_relat_1(sK2)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.33/0.53  fof(f106,plain,(
% 1.33/0.53    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl9_3),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f70,f31])).
% 1.33/0.53  fof(f31,plain,(
% 1.33/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.33/0.53    inference(equality_resolution,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.33/0.53  fof(f70,plain,(
% 1.33/0.53    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | ~spl9_3),
% 1.33/0.53    inference(avatar_component_clause,[],[f69])).
% 1.33/0.53  fof(f69,plain,(
% 1.33/0.53    spl9_3 <=> ! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.33/0.53  fof(f49,plain,(
% 1.33/0.53    r2_hidden(sK3,sK1) | ~spl9_1),
% 1.33/0.53    inference(avatar_component_clause,[],[f47])).
% 1.33/0.53  fof(f47,plain,(
% 1.33/0.53    spl9_1 <=> r2_hidden(sK3,sK1)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.53    inference(equality_resolution,[],[f22])).
% 1.33/0.53  fof(f22,plain,(
% 1.33/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.53  fof(f94,plain,(
% 1.33/0.53    spl9_2 | ~spl9_4),
% 1.33/0.53    inference(avatar_contradiction_clause,[],[f92])).
% 1.33/0.53  fof(f92,plain,(
% 1.33/0.53    $false | (spl9_2 | ~spl9_4)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f66,f75,f88])).
% 1.33/0.53  fof(f88,plain,(
% 1.33/0.53    ( ! [X3] : (r2_hidden(k4_tarski(sK4(X3),X3),sK2) | ~r2_hidden(X3,sK1)) ) | ~spl9_4),
% 1.33/0.53    inference(avatar_component_clause,[],[f87])).
% 1.33/0.53  fof(f87,plain,(
% 1.33/0.53    spl9_4 <=> ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2))),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.33/0.53  fof(f75,plain,(
% 1.33/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK8(sK1,k2_relat_1(sK2))),sK2)) ) | spl9_2),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f67,f32])).
% 1.33/0.53  fof(f32,plain,(
% 1.33/0.53    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) )),
% 1.33/0.53    inference(equality_resolution,[],[f18])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.53  fof(f67,plain,(
% 1.33/0.53    ~r2_hidden(sK8(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | spl9_2),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f62,f28])).
% 1.33/0.53  fof(f28,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f12])).
% 1.33/0.53  fof(f62,plain,(
% 1.33/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl9_2),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f53,f58,f24])).
% 1.33/0.53  fof(f24,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f2])).
% 1.33/0.53  fof(f58,plain,(
% 1.33/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f44,f30])).
% 1.33/0.53  fof(f30,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f3])).
% 1.33/0.53  fof(f3,axiom,(
% 1.33/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.33/0.53    inference(forward_demodulation,[],[f35,f36])).
% 1.33/0.53  fof(f36,plain,(
% 1.33/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f16,f17])).
% 1.33/0.53  fof(f17,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f10])).
% 1.33/0.53  fof(f10,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f6])).
% 1.33/0.53  fof(f6,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.53  fof(f16,plain,(
% 1.33/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.53    inference(cnf_transformation,[],[f9])).
% 1.33/0.53  fof(f9,plain,(
% 1.33/0.53    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,negated_conjecture,(
% 1.33/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.33/0.53    inference(negated_conjecture,[],[f7])).
% 1.33/0.53  fof(f7,conjecture,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f16,f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f11])).
% 1.33/0.53  fof(f11,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.33/0.53  fof(f53,plain,(
% 1.33/0.53    sK1 != k2_relat_1(sK2) | spl9_2),
% 1.33/0.53    inference(avatar_component_clause,[],[f51])).
% 1.33/0.53  fof(f66,plain,(
% 1.33/0.53    r2_hidden(sK8(sK1,k2_relat_1(sK2)),sK1) | spl9_2),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f62,f27])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f12])).
% 1.33/0.53  fof(f89,plain,(
% 1.33/0.53    spl9_4 | spl9_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f43,f51,f87])).
% 1.33/0.53  fof(f43,plain,(
% 1.33/0.53    ( ! [X3] : (sK1 = k2_relat_1(sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) )),
% 1.33/0.53    inference(backward_demodulation,[],[f15,f36])).
% 1.33/0.53  fof(f15,plain,(
% 1.33/0.53    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(sK4(X3),X3),sK2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f9])).
% 1.33/0.53  fof(f71,plain,(
% 1.33/0.53    spl9_3 | ~spl9_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f42,f51,f69])).
% 1.33/0.53  fof(f42,plain,(
% 1.33/0.53    ( ! [X4] : (sK1 != k2_relat_1(sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 1.33/0.53    inference(backward_demodulation,[],[f14,f36])).
% 1.33/0.53  fof(f14,plain,(
% 1.33/0.53    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f9])).
% 1.33/0.53  fof(f54,plain,(
% 1.33/0.53    spl9_1 | ~spl9_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f41,f51,f47])).
% 1.33/0.53  fof(f41,plain,(
% 1.33/0.53    sK1 != k2_relat_1(sK2) | r2_hidden(sK3,sK1)),
% 1.33/0.53    inference(backward_demodulation,[],[f13,f36])).
% 1.33/0.53  fof(f13,plain,(
% 1.33/0.53    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f9])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (30310)------------------------------
% 1.33/0.53  % (30310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (30310)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (30310)Memory used [KB]: 6268
% 1.33/0.53  % (30310)Time elapsed: 0.128 s
% 1.33/0.53  % (30310)------------------------------
% 1.33/0.53  % (30310)------------------------------
% 1.33/0.53  % (30309)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.53  % (30305)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.54  % (30301)Success in time 0.176 s
%------------------------------------------------------------------------------
