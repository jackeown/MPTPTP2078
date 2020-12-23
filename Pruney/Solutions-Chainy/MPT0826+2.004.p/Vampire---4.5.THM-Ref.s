%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 (  94 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :  164 ( 230 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f48,f56,f60,f72,f81,f86,f91,f94])).

fof(f94,plain,
    ( spl1_1
    | ~ spl1_14 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl1_1
    | ~ spl1_14 ),
    inference(resolution,[],[f90,f27])).

fof(f27,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f90,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl1_14
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f91,plain,
    ( spl1_14
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f87,f84,f70,f89])).

fof(f70,plain,
    ( spl1_11
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f84,plain,
    ( spl1_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f87,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(resolution,[],[f85,f71])).

fof(f71,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl1_13
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f82,f79,f70,f84])).

fof(f79,plain,
    ( spl1_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(resolution,[],[f80,f71])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f77,f58,f46,f42,f30,f79])).

fof(f30,plain,
    ( spl1_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f58,plain,
    ( spl1_9
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relat_1(X2),X1)
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f76,f47])).

fof(f47,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X2)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f75,f43])).

fof(f43,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X2)
        | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(resolution,[],[f59,f31])).

fof(f31,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(k2_relat_1(X2),X1)
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f72,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f68,f54,f38,f34,f70])).

fof(f34,plain,
    ( spl1_3
  <=> ! [X0] : k2_subset_1(X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f38,plain,
    ( spl1_4
  <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f54,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f68,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f66,f35])).

fof(f35,plain,
    ( ! [X0] : k2_subset_1(X0) = X0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k2_subset_1(X0),X0)
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,
    ( ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f60,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f56,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f28,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
   => ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:59:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (28163)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (28161)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (28161)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f48,f56,f60,f72,f81,f86,f91,f94])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl1_1 | ~spl1_14),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    $false | (spl1_1 | ~spl1_14)),
% 0.21/0.42    inference(resolution,[],[f90,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl1_1 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl1_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl1_14 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl1_14 | ~spl1_11 | ~spl1_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f87,f84,f70,f89])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl1_11 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl1_13 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | (~spl1_11 | ~spl1_13)),
% 0.21/0.42    inference(resolution,[],[f85,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl1_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl1_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f84])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl1_13 | ~spl1_11 | ~spl1_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f82,f79,f70,f84])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl1_12 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl1_11 | ~spl1_12)),
% 0.21/0.42    inference(resolution,[],[f80,f71])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | ~spl1_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f79])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl1_12 | ~spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f77,f58,f46,f42,f30,f79])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl1_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl1_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl1_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl1_9 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_9)),
% 0.21/0.42    inference(forward_demodulation,[],[f76,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(k1_relat_1(k6_relat_1(X0)),X2) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl1_2 | ~spl1_5 | ~spl1_9)),
% 0.21/0.42    inference(forward_demodulation,[],[f75,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~r1_tarski(k1_relat_1(k6_relat_1(X0)),X2) | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl1_2 | ~spl1_9)),
% 0.21/0.42    inference(resolution,[],[f59,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl1_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl1_11 | ~spl1_3 | ~spl1_4 | ~spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f68,f54,f38,f34,f70])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl1_3 <=> ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl1_4 <=> ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl1_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_8)),
% 0.21/0.42    inference(forward_demodulation,[],[f66,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) ) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k2_subset_1(X0),X0)) ) | (~spl1_4 | ~spl1_8)),
% 0.21/0.42    inference(resolution,[],[f55,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) ) | ~spl1_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl1_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f54])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.42    inference(nnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f46])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f42])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0] : ~m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : ~m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (28161)------------------------------
% 0.21/0.43  % (28161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (28161)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (28161)Memory used [KB]: 10618
% 0.21/0.43  % (28161)Time elapsed: 0.007 s
% 0.21/0.43  % (28161)------------------------------
% 0.21/0.43  % (28161)------------------------------
% 0.21/0.43  % (28152)Success in time 0.065 s
%------------------------------------------------------------------------------
