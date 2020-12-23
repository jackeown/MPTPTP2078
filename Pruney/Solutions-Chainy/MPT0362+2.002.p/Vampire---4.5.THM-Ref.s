%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 236 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f268,f297,f318,f327])).

fof(f327,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f44,f56,f267,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f267,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f56,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f21,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f318,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f298,f302,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f302,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f44,f263,f35])).

fof(f263,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl6_2
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f298,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f67,f258,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f258,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl6_1
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f67,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f297,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f270,f269,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f269,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK1,sK2),sK1),k3_xboole_0(sK1,sK2))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f259,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f259,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f257])).

fof(f270,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),sK1),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f259,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f268,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f89,f265,f261,f257])).

fof(f89,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(resolution,[],[f54,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f54,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f20,f50])).

fof(f50,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:03:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (30263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (30263)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (30278)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (30287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (30270)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (30273)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (30282)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (30265)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (30261)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (30260)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (30271)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f268,f297,f318,f327])).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    spl6_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f322])).
% 0.20/0.52  fof(f322,plain,(
% 0.20/0.52    $false | spl6_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f44,f56,f267,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl6_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f265])).
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    spl6_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f44,f21,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    ~spl6_1 | spl6_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f312])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    $false | (~spl6_1 | spl6_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f298,f302,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    ~r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl6_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f44,f263,f35])).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f261])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    spl6_2 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    r1_tarski(k3_xboole_0(sK1,sK2),sK0) | ~spl6_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f67,f258,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.52  fof(f258,plain,(
% 0.20/0.52    r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f257])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    spl6_1 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f56,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    spl6_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f288])).
% 0.20/0.52  fof(f288,plain,(
% 0.20/0.52    $false | spl6_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f270,f269,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    r2_hidden(sK4(k3_xboole_0(sK1,sK2),sK1),k3_xboole_0(sK1,sK2)) | spl6_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f259,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f259,plain,(
% 0.20/0.52    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f257])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    ~r2_hidden(sK4(k3_xboole_0(sK1,sK2),sK1),sK1) | spl6_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f259,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f268,plain,(
% 0.20/0.52    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f89,f265,f261,f257])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 0.20/0.52    inference(resolution,[],[f54,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))),
% 0.20/0.52    inference(backward_demodulation,[],[f20,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f19,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (30263)------------------------------
% 0.20/0.52  % (30263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30263)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (30263)Memory used [KB]: 6396
% 0.20/0.52  % (30263)Time elapsed: 0.108 s
% 0.20/0.53  % (30263)------------------------------
% 0.20/0.53  % (30263)------------------------------
% 0.20/0.53  % (30254)Success in time 0.17 s
%------------------------------------------------------------------------------
