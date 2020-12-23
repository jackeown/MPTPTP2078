%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  55 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f48])).

fof(f48,plain,(
    spl0_2 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl0_2 ),
    inference(subsumption_resolution,[],[f28,f32])).

fof(f32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f17,f21,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f28,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl0_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl0_2
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).

fof(f46,plain,(
    ~ spl0_2 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | ~ spl0_2 ),
    inference(subsumption_resolution,[],[f44,f14])).

fof(f14,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f44,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl0_2 ),
    inference(forward_demodulation,[],[f43,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f43,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_2 ),
    inference(forward_demodulation,[],[f42,f15])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f42,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl0_2 ),
    inference(forward_demodulation,[],[f35,f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl0_2 ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (10588)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.42  % (10587)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.42  % (10587)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f46,f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl0_2),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    $false | spl0_2),
% 0.22/0.42    inference(subsumption_resolution,[],[f28,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f17,f21,f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ~v1_relat_1(k1_xboole_0) | spl0_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    spl0_2 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ~spl0_2),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    $false | ~spl0_2),
% 0.22/0.42    inference(subsumption_resolution,[],[f44,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(flattening,[],[f9])).
% 0.22/0.42  fof(f9,negated_conjecture,(
% 0.22/0.42    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(negated_conjecture,[],[f8])).
% 0.22/0.42  fof(f8,conjecture,(
% 0.22/0.42    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    k1_xboole_0 = k3_relat_1(k1_xboole_0) | ~spl0_2),
% 0.22/0.42    inference(forward_demodulation,[],[f43,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl0_2),
% 0.22/0.42    inference(forward_demodulation,[],[f42,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl0_2),
% 0.22/0.42    inference(forward_demodulation,[],[f35,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl0_2),
% 0.22/0.42    inference(resolution,[],[f19,f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0) | ~spl0_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f27])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (10587)------------------------------
% 0.22/0.42  % (10587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (10587)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (10587)Memory used [KB]: 6012
% 0.22/0.42  % (10587)Time elapsed: 0.004 s
% 0.22/0.42  % (10587)------------------------------
% 0.22/0.42  % (10587)------------------------------
% 0.22/0.42  % (10584)Success in time 0.062 s
%------------------------------------------------------------------------------
