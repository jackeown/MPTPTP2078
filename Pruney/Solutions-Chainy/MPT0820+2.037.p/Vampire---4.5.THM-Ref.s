%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 258 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f95,f106,f113])).

fof(f113,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f108,f45])).

fof(f45,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

fof(f108,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl3_4 ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f107,plain,
    ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f105,f58])).

fof(f58,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK2,X0)
        | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_4
  <=> ! [X0] :
        ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)
        | ~ v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f101,f93,f104,f69])).

fof(f69,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f93,plain,
    ( spl3_3
  <=> ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( ! [X0] :
        ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)
        | ~ v5_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f100,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f97,plain,
    ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f96,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f96,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2))))
    | ~ spl3_3 ),
    inference(resolution,[],[f94,f57])).

fof(f57,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f89,f93,f69])).

fof(f89,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
      | ~ v4_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f87,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) ) ),
    inference(superposition,[],[f47,f62])).

fof(f62,plain,(
    k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f34,f34])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f77,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (30858)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (30869)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (30856)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (30856)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f77,f95,f106,f113])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~spl3_4),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    $false | ~spl3_4),
% 0.22/0.47    inference(resolution,[],[f108,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.22/0.47    inference(definition_unfolding,[],[f30,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f12])).
% 0.22/0.47  fof(f12,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | ~spl3_4),
% 0.22/0.47    inference(resolution,[],[f107,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f41,f34])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1) | ~spl3_4),
% 0.22/0.47    inference(resolution,[],[f105,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    v5_relat_1(sK2,sK1)),
% 0.22/0.47    inference(resolution,[],[f43,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)) ) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f104])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    spl3_4 <=> ! [X0] : (r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) | ~v5_relat_1(sK2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ~spl3_1 | spl3_4 | ~spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f101,f93,f104,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    spl3_3 <=> ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~v4_relat_1(sK2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f100,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)) ) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f97,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2)) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f96,f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f40,f34])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2)))) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f94,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    v4_relat_1(sK2,sK0)),
% 0.22/0.47    inference(resolution,[],[f42,f29])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    ( ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f93])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    ~spl3_1 | spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f89,f93,f69])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.22/0.47    inference(resolution,[],[f87,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))) )),
% 0.22/0.47    inference(superposition,[],[f47,f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.22/0.47    inference(resolution,[],[f46,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    v1_relat_1(sK2)),
% 0.22/0.47    inference(resolution,[],[f50,f29])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.22/0.47    inference(resolution,[],[f32,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f31,f34])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f39,f34,f34])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    $false | spl3_1),
% 0.22/0.47    inference(resolution,[],[f71,f51])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f69])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (30856)------------------------------
% 0.22/0.47  % (30856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (30856)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (30856)Memory used [KB]: 6140
% 0.22/0.47  % (30856)Time elapsed: 0.053 s
% 0.22/0.47  % (30856)------------------------------
% 0.22/0.47  % (30856)------------------------------
% 0.22/0.47  % (30852)Success in time 0.114 s
%------------------------------------------------------------------------------
