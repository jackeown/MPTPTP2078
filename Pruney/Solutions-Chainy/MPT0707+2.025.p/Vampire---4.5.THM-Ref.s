%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 134 expanded)
%              Number of equality atoms :   39 (  59 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f50,f58,f71])).

fof(f71,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f69,f49])).

fof(f49,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_3
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f69,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f62,f19])).

fof(f19,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f62,plain,
    ( k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_4 ),
    inference(superposition,[],[f19,f57])).

fof(f57,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_4
  <=> k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f58,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f53,f32,f55])).

fof(f32,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f53,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f51,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK1,sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f37,f22])).

fof(f22,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f36,f18])).

fof(f18,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f50,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f45,f27,f47])).

fof(f27,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(superposition,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f43,f19])).

fof(f43,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f42,f22])).

fof(f42,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f40,f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f39,f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f20,f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f29,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (27700)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (27705)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (27700)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f30,f35,f50,f58,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl2_3 | ~spl2_4),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    $false | (spl2_3 | ~spl2_4)),
% 0.21/0.42    inference(subsumption_resolution,[],[f69,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    sK1 != k3_xboole_0(sK0,sK1) | spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_3 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_4),
% 0.21/0.42    inference(forward_demodulation,[],[f62,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1)) | ~spl2_4),
% 0.21/0.42    inference(superposition,[],[f19,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl2_4 <=> k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_4 | ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f53,f32,f55])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_2),
% 0.21/0.42    inference(forward_demodulation,[],[f51,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK1,sK0)) | ~spl2_2),
% 0.21/0.42    inference(resolution,[],[f41,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(resolution,[],[f38,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f37,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f36,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.21/0.42    inference(resolution,[],[f23,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ~spl2_3 | spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f45,f27,f47])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    sK1 != k3_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.42    inference(superposition,[],[f29,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f43,f19])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f42,f22])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.42    inference(resolution,[],[f40,f16])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f39,f19])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1)))) )),
% 0.21/0.42    inference(resolution,[],[f20,f16])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f32])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f27])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (27700)------------------------------
% 0.21/0.42  % (27700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (27700)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (27700)Memory used [KB]: 10618
% 0.21/0.42  % (27700)Time elapsed: 0.007 s
% 0.21/0.42  % (27700)------------------------------
% 0.21/0.42  % (27700)------------------------------
% 0.21/0.43  % (27698)Success in time 0.064 s
%------------------------------------------------------------------------------
