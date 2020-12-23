%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 138 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 290 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f63,f76,f84,f90,f108,f123,f131,f370])).

fof(f370,plain,
    ( spl3_1
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f369,f127,f119,f87,f48])).

fof(f48,plain,
    ( spl3_1
  <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( spl3_6
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f119,plain,
    ( spl3_9
  <=> k3_relat_1(sK2) = k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f127,plain,
    ( spl3_10
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f369,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f368,f121])).

fof(f121,plain,
    ( k3_relat_1(sK2) = k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f368,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f338,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f338,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))),k3_tarski(k2_tarski(sK1,sK0)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f155,f178,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f178,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK1,X0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f111,f33])).

fof(f111,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(X0,sK1)))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f89,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f89,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f155,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(X0,sK0)))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f129,f45])).

fof(f129,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f131,plain,
    ( ~ spl3_3
    | spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f125,f104,f127,f60])).

fof(f60,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f104,plain,
    ( spl3_8
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f125,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f35,f106])).

fof(f106,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f123,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f117,f60,f119])).

fof(f117,plain,
    ( k3_relat_1(sK2) = k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f109,f62])).

fof(f62,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f44,f33])).

fof(f44,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f108,plain,
    ( ~ spl3_3
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f102,f72,f104,f60])).

fof(f72,plain,
    ( spl3_4
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f102,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f38,f74])).

fof(f74,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f90,plain,
    ( spl3_6
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f85,f80,f60,f87])).

fof(f80,plain,
    ( spl3_5
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f62,f82,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f82,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f84,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f78,f53,f80])).

fof(f53,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f41,plain,(
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

fof(f76,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f53,f72])).

fof(f70,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f40,f55])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f53,f60])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f32,f55,f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
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

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f48])).

fof(f43,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (1480)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (1487)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (1479)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (1488)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (1485)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (1476)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (1480)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (1485)Refutation not found, incomplete strategy% (1485)------------------------------
% 0.22/0.49  % (1485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (1485)Memory used [KB]: 10618
% 0.22/0.49  % (1485)Time elapsed: 0.072 s
% 0.22/0.49  % (1485)------------------------------
% 0.22/0.49  % (1485)------------------------------
% 0.22/0.50  % (1478)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f51,f56,f63,f76,f84,f90,f108,f123,f131,f370])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    spl3_1 | ~spl3_6 | ~spl3_9 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f369,f127,f119,f87,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl3_1 <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl3_6 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl3_9 <=> k3_relat_1(sK2) = k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl3_10 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | (~spl3_6 | ~spl3_9 | ~spl3_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f368,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    k3_relat_1(sK2) = k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f368,plain,(
% 0.22/0.50    r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) | (~spl3_6 | ~spl3_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f338,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))),k3_tarski(k2_tarski(sK1,sK0))) | (~spl3_6 | ~spl3_10)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f155,f178,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f42,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK1,X0)))) ) | ~spl3_6),
% 0.22/0.50    inference(superposition,[],[f111,f33])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(X0,sK1)))) ) | ~spl3_6),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f89,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f39,f34])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f87])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(X0,sK0)))) ) | ~spl3_10),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f129,f45])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f127])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~spl3_3 | spl3_10 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f125,f104,f127,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl3_8 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl3_8),
% 0.22/0.50    inference(superposition,[],[f35,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    sK2 = k7_relat_1(sK2,sK0) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f104])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl3_9 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f117,f60,f119])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    k3_relat_1(sK2) = k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f109,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f44,f33])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f30,f34])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~spl3_3 | spl3_8 | ~spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f102,f72,f104,f60])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl3_4 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.50    inference(resolution,[],[f38,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    v4_relat_1(sK2,sK0) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl3_6 | ~spl3_3 | ~spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f85,f80,f60,f87])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_5 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_3 | ~spl3_5)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f62,f82,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK1) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl3_5 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f78,f53,f80])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK1) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f41,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl3_4 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f70,f53,f72])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    v4_relat_1(sK2,sK0) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f40,f55])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_3 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f53,f60])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl3_2),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f32,f55,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f53])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f48])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.22/0.50    inference(definition_unfolding,[],[f29,f34])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (1480)------------------------------
% 0.22/0.50  % (1480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1480)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (1480)Memory used [KB]: 6396
% 0.22/0.50  % (1480)Time elapsed: 0.068 s
% 0.22/0.50  % (1480)------------------------------
% 0.22/0.50  % (1480)------------------------------
% 0.22/0.50  % (1473)Success in time 0.135 s
%------------------------------------------------------------------------------
