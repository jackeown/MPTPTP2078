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
% DateTime   : Thu Dec  3 12:44:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 155 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f73,f81,f113])).

fof(f113,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f74,f75,f88,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f40,f83,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f80,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_3
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f75,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK1),k4_xboole_0(X0,sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f74,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f61,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f53,f78,f59])).

fof(f53,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f42,f49])).

fof(f49,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f18,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f26,f57])).

fof(f57,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f62,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f59,f55])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (15646)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (15646)Refutation not found, incomplete strategy% (15646)------------------------------
% 0.22/0.50  % (15646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15639)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (15646)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15646)Memory used [KB]: 10746
% 0.22/0.50  % (15646)Time elapsed: 0.086 s
% 0.22/0.50  % (15646)------------------------------
% 0.22/0.50  % (15646)------------------------------
% 0.22/0.51  % (15639)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f62,f73,f81,f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl5_2 | ~spl5_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    $false | (spl5_2 | ~spl5_3)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f74,f75,f88,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | ~spl5_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f40,f83,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | ~spl5_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f80,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl5_3 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK3(sK1),k4_xboole_0(X0,sK1))) ) | spl5_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f74,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    r2_hidden(sK3(sK1),sK1) | spl5_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f61,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl5_2 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl5_2 | spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f78,f59])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(backward_demodulation,[],[f42,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f18,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl5_1),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    $false | spl5_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f26,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl5_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ~spl5_1 | ~spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f59,f55])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.51    inference(inner_rewriting,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f19,f21])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (15639)------------------------------
% 0.22/0.51  % (15639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15639)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (15639)Memory used [KB]: 6268
% 0.22/0.51  % (15639)Time elapsed: 0.096 s
% 0.22/0.51  % (15639)------------------------------
% 0.22/0.51  % (15639)------------------------------
% 0.22/0.51  % (15634)Success in time 0.15 s
%------------------------------------------------------------------------------
