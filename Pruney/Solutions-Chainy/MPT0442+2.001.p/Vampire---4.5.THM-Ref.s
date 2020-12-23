%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  75 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 210 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f105,f118])).

fof(f118,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f77,f65,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_2
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,(
    m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f74,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f26,f49])).

fof(f49,plain,(
    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f41,f46])).

fof(f46,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f41,plain,(
    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f17,f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f105,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f68,f99,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f99,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK0),k2_relat_1(sK1))),sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f18,f83,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f83,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK0),k2_relat_1(sK1))),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f61,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_1
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f68,plain,
    ( r2_hidden(sK5(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f16,f63,f59])).

fof(f16,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:03:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (15303)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.49  % (15293)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (15293)Refutation not found, incomplete strategy% (15293)------------------------------
% 0.19/0.50  % (15293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (15319)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.50  % (15308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.50  % (15293)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (15293)Memory used [KB]: 1791
% 0.19/0.50  % (15293)Time elapsed: 0.100 s
% 0.19/0.50  % (15293)------------------------------
% 0.19/0.50  % (15293)------------------------------
% 0.19/0.50  % (15294)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (15300)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (15298)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (15315)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (15297)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (15315)Refutation not found, incomplete strategy% (15315)------------------------------
% 0.19/0.50  % (15315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (15315)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (15315)Memory used [KB]: 10618
% 0.19/0.50  % (15315)Time elapsed: 0.070 s
% 0.19/0.50  % (15315)------------------------------
% 0.19/0.50  % (15315)------------------------------
% 0.19/0.51  % (15297)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f119,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f66,f105,f118])).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    spl6_2),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f112])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    $false | spl6_2),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f77,f65,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | spl6_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    spl6_2 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK1)))),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f74,f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.51    inference(superposition,[],[f26,f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.51    inference(backward_demodulation,[],[f41,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    sK1 = k2_xboole_0(sK0,sK1)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f18,f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    r1_tarski(sK0,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f10])).
% 0.19/0.51  fof(f10,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.51    inference(negated_conjecture,[],[f8])).
% 0.19/0.51  fof(f8,conjecture,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f17,f19,f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    v1_relat_1(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    v1_relat_1(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    spl6_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f103])).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    $false | spl6_1),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f68,f99,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.19/0.51    inference(equality_resolution,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK0),k2_relat_1(sK1))),sK0)) ) | spl6_1),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f18,f83,f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK0),k2_relat_1(sK1))),sK1)) ) | spl6_1),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f69,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ~r2_hidden(sK5(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl6_1),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f61,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl6_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f59])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    spl6_1 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    r2_hidden(sK5(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0)) | spl6_1),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f61,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ~spl6_1 | ~spl6_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f16,f63,f59])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (15297)------------------------------
% 0.19/0.51  % (15297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15297)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (15297)Memory used [KB]: 6268
% 0.19/0.51  % (15297)Time elapsed: 0.111 s
% 0.19/0.51  % (15297)------------------------------
% 0.19/0.51  % (15297)------------------------------
% 0.19/0.51  % (15292)Success in time 0.157 s
%------------------------------------------------------------------------------
