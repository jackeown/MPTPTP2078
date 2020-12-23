%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:14 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 239 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f36,f47,f105])).

fof(f105,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f103,f48])).

fof(f48,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f30,f39])).

fof(f39,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f22,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f30,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f103,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(resolution,[],[f102,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f102,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f100,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | spl3_2 ),
    inference(resolution,[],[f96,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f96,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2 ),
    inference(forward_demodulation,[],[f95,f40])).

fof(f40,plain,(
    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(resolution,[],[f22,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f94,f19])).

fof(f94,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f91,f18])).

fof(f91,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(superposition,[],[f49,f39])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl3_2 ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f47,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f44,f34])).

fof(f34,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f44,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_1 ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f42,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(superposition,[],[f29,f39])).

fof(f29,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f36,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f32,f28])).

fof(f17,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f16,f32,f28])).

fof(f16,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (18476)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.14/0.42  % (18484)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.14/0.42  % (18476)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f106,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f35,f36,f47,f105])).
% 0.14/0.42  fof(f105,plain,(
% 0.14/0.42    ~spl3_1 | spl3_2),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f104])).
% 0.14/0.42  fof(f104,plain,(
% 0.14/0.42    $false | (~spl3_1 | spl3_2)),
% 0.14/0.42    inference(subsumption_resolution,[],[f103,f48])).
% 0.14/0.42  fof(f48,plain,(
% 0.14/0.42    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_1),
% 0.14/0.42    inference(forward_demodulation,[],[f30,f39])).
% 0.14/0.42  fof(f39,plain,(
% 0.14/0.42    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.14/0.42    inference(resolution,[],[f22,f18])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.14/0.42    inference(cnf_transformation,[],[f9])).
% 0.14/0.42  fof(f9,plain,(
% 0.14/0.42    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.42    inference(ennf_transformation,[],[f8])).
% 0.14/0.42  fof(f8,negated_conjecture,(
% 0.14/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.14/0.42    inference(negated_conjecture,[],[f7])).
% 0.14/0.42  fof(f7,conjecture,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.14/0.42  fof(f22,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f11])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.42    inference(ennf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.14/0.42  fof(f30,plain,(
% 0.14/0.42    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl3_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f28])).
% 0.14/0.42  fof(f28,plain,(
% 0.14/0.42    spl3_1 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.14/0.42  fof(f103,plain,(
% 0.14/0.42    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 0.14/0.42    inference(resolution,[],[f102,f21])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f10])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.14/0.42  fof(f102,plain,(
% 0.14/0.42    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 0.14/0.42    inference(subsumption_resolution,[],[f100,f20])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.14/0.42  fof(f100,plain,(
% 0.14/0.42    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | spl3_2),
% 0.14/0.42    inference(resolution,[],[f96,f26])).
% 0.14/0.42  fof(f26,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f15])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.14/0.42    inference(flattening,[],[f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.14/0.42    inference(ennf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,axiom,(
% 0.14/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.14/0.42  fof(f96,plain,(
% 0.14/0.42    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl3_2),
% 0.14/0.42    inference(forward_demodulation,[],[f95,f40])).
% 0.14/0.42  fof(f40,plain,(
% 0.14/0.42    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)),
% 0.14/0.42    inference(resolution,[],[f22,f19])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.14/0.42    inference(cnf_transformation,[],[f9])).
% 0.14/0.42  fof(f95,plain,(
% 0.14/0.42    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.14/0.42    inference(subsumption_resolution,[],[f94,f19])).
% 0.14/0.42  fof(f94,plain,(
% 0.14/0.42    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_2),
% 0.14/0.42    inference(subsumption_resolution,[],[f91,f18])).
% 0.14/0.42  fof(f91,plain,(
% 0.14/0.42    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_2),
% 0.14/0.42    inference(superposition,[],[f49,f39])).
% 0.14/0.42  fof(f49,plain,(
% 0.14/0.42    ( ! [X0] : (~r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | spl3_2),
% 0.14/0.42    inference(resolution,[],[f23,f33])).
% 0.14/0.42  fof(f33,plain,(
% 0.14/0.42    ~r1_tarski(sK1,sK2) | spl3_2),
% 0.14/0.42    inference(avatar_component_clause,[],[f32])).
% 0.14/0.42  fof(f32,plain,(
% 0.14/0.42    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.14/0.42    inference(ennf_transformation,[],[f6])).
% 0.14/0.42  fof(f6,axiom,(
% 0.14/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.14/0.42  fof(f47,plain,(
% 0.14/0.42    spl3_1 | ~spl3_2),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f46])).
% 0.14/0.42  fof(f46,plain,(
% 0.14/0.42    $false | (spl3_1 | ~spl3_2)),
% 0.14/0.42    inference(subsumption_resolution,[],[f44,f34])).
% 0.14/0.42  fof(f34,plain,(
% 0.14/0.42    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.14/0.42    inference(avatar_component_clause,[],[f32])).
% 0.14/0.42  fof(f44,plain,(
% 0.14/0.42    ~r1_tarski(sK1,sK2) | spl3_1),
% 0.14/0.42    inference(resolution,[],[f42,f25])).
% 0.14/0.42  fof(f25,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.14/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.14/0.42  fof(f42,plain,(
% 0.14/0.42    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_1),
% 0.14/0.42    inference(superposition,[],[f29,f39])).
% 0.14/0.42  fof(f29,plain,(
% 0.14/0.42    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f28])).
% 0.14/0.42  fof(f36,plain,(
% 0.14/0.42    ~spl3_1 | ~spl3_2),
% 0.14/0.42    inference(avatar_split_clause,[],[f17,f32,f28])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.14/0.42    inference(cnf_transformation,[],[f9])).
% 0.14/0.42  fof(f35,plain,(
% 0.14/0.42    spl3_1 | spl3_2),
% 0.14/0.42    inference(avatar_split_clause,[],[f16,f32,f28])).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.14/0.42    inference(cnf_transformation,[],[f9])).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (18476)------------------------------
% 0.14/0.42  % (18476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (18476)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (18476)Memory used [KB]: 10618
% 0.14/0.42  % (18476)Time elapsed: 0.006 s
% 0.14/0.42  % (18476)------------------------------
% 0.14/0.42  % (18476)------------------------------
% 0.22/0.42  % (18475)Success in time 0.064 s
%------------------------------------------------------------------------------
