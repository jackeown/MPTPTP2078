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
% DateTime   : Thu Dec  3 12:56:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 170 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 428 expanded)
%              Number of equality atoms :   27 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f71,f101,f121,f150])).

fof(f150,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f42,f58,f138,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f138,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f130,f61])).

fof(f61,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl9_2
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f130,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f70,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f70,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl9_3
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f58,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_1
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
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

fof(f121,plain,
    ( spl9_2
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl9_2
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f77,f104,f100])).

fof(f100,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK4(X3)),sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_6
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK8(sK1,k1_relat_1(sK2)),X0),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f78,f44])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,
    ( ~ r2_hidden(sK8(sK1,k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f75,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f62,f73,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(superposition,[],[f64,f65])).

% (28992)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f65,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f48,f45,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f45,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f23,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f36,f23,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f62,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f77,plain,
    ( r2_hidden(sK8(sK1,k1_relat_1(sK2)),sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f75,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,
    ( spl9_6
    | spl9_2 ),
    inference(avatar_split_clause,[],[f54,f60,f99])).

fof(f54,plain,(
    ! [X3] :
      ( sK1 = k1_relat_1(sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    inference(backward_demodulation,[],[f22,f47])).

fof(f47,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f22,plain,(
    ! [X3] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f53,f60,f69])).

fof(f53,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(backward_demodulation,[],[f21,f47])).

fof(f21,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f52,f60,f56])).

fof(f52,plain,
    ( sK1 != k1_relat_1(sK2)
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f20,f47])).

fof(f20,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (28999)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (29007)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (29013)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29005)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (28995)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (28997)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (28994)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28990)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (28994)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f63,f71,f101,f121,f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    $false | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f42,f58,f138,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK1) | (~spl9_2 | ~spl9_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f130,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    sK1 = k1_relat_1(sK2) | ~spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl9_2 <=> sK1 = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl9_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) ) | ~spl9_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl9_3 <=> ! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    r2_hidden(sK3,sK1) | ~spl9_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl9_1 <=> r2_hidden(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl9_2 | ~spl9_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    $false | (spl9_2 | ~spl9_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f77,f104,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK4(X3)),sK2) | ~r2_hidden(X3,sK1)) ) | ~spl9_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl9_6 <=> ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK8(sK1,k1_relat_1(sK2)),X0),sK2)) ) | spl9_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f78,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~r2_hidden(sK8(sK1,k1_relat_1(sK2)),k1_relat_1(sK2)) | spl9_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f75,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl9_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f62,f73,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.21/0.52    inference(superposition,[],[f64,f65])).
% 0.21/0.52  % (28992)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    sK2 = k7_relat_1(sK2,sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f45,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v4_relat_1(sK2,sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f23,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f36,f23,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    sK1 != k1_relat_1(sK2) | spl9_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f60])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    r2_hidden(sK8(sK1,k1_relat_1(sK2)),sK1) | spl9_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f75,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl9_6 | spl9_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f54,f60,f99])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X3] : (sK1 = k1_relat_1(sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f22,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f23,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X3] : (sK1 = k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(k4_tarski(X3,sK4(X3)),sK2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl9_3 | ~spl9_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f60,f69])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X4] : (sK1 != k1_relat_1(sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f21,f47])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl9_1 | ~spl9_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f60,f56])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    sK1 != k1_relat_1(sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f20,f47])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28994)------------------------------
% 0.21/0.52  % (28994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28994)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28994)Memory used [KB]: 6268
% 0.21/0.52  % (28994)Time elapsed: 0.118 s
% 0.21/0.52  % (28994)------------------------------
% 0.21/0.52  % (28994)------------------------------
% 0.21/0.52  % (29015)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (28989)Success in time 0.164 s
%------------------------------------------------------------------------------
