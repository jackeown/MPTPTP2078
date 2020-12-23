%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 161 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f62,f79,f107,f187,f222])).

fof(f222,plain,
    ( ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f212,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f71,f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f71,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k5_xboole_0(X5,X6)))
      | ~ r2_hidden(X4,X6)
      | ~ r2_hidden(X4,X7)
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f212,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f38,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f38,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f187,plain,
    ( ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f106,f38])).

fof(f106,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_11
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f107,plain,
    ( spl2_11
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f95,f76,f105])).

fof(f76,plain,
    ( spl2_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f95,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl2_8 ),
    inference(resolution,[],[f78,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f78,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f79,plain,
    ( spl2_8
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f74,f55,f36,f76])).

fof(f55,plain,
    ( spl2_5
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f74,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_2
    | spl2_5 ),
    inference(subsumption_resolution,[],[f73,f38])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | v1_xboole_0(sK1)
    | spl2_5 ),
    inference(resolution,[],[f57,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f57,plain,
    ( ~ m1_subset_1(sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f62,plain,
    ( ~ spl2_5
    | spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f53,f31,f59,f55])).

fof(f31,plain,
    ( spl2_1
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK0,sK1)
    | spl2_1 ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:01:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.41  % (13718)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (13725)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (13718)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f236,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f34,f39,f62,f79,f107,f187,f222])).
% 0.21/0.42  fof(f222,plain,(
% 0.21/0.42    ~spl2_2 | ~spl2_6),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f221])).
% 0.21/0.42  fof(f221,plain,(
% 0.21/0.42    $false | (~spl2_2 | ~spl2_6)),
% 0.21/0.42    inference(subsumption_resolution,[],[f212,f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X2)) )),
% 0.21/0.42    inference(resolution,[],[f71,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k5_xboole_0(X5,X6))) | ~r2_hidden(X4,X6) | ~r2_hidden(X4,X7) | ~r2_hidden(X4,X5)) )),
% 0.21/0.42    inference(resolution,[],[f27,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.42  fof(f212,plain,(
% 0.21/0.42    r2_hidden(sK0,k1_xboole_0) | (~spl2_2 | ~spl2_6)),
% 0.21/0.42    inference(superposition,[],[f38,f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    k1_xboole_0 = sK1 | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl2_6 <=> k1_xboole_0 = sK1),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f187,plain,(
% 0.21/0.42    ~spl2_2 | ~spl2_11),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.42  fof(f181,plain,(
% 0.21/0.42    $false | (~spl2_2 | ~spl2_11)),
% 0.21/0.42    inference(resolution,[],[f106,f38])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f105])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl2_11 <=> ! [X2] : ~r2_hidden(X2,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl2_11 | ~spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f95,f76,f105])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl2_8 <=> v1_xboole_0(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl2_8),
% 0.21/0.42    inference(resolution,[],[f78,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    v1_xboole_0(sK1) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl2_8 | ~spl2_2 | spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f74,f55,f36,f76])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl2_5 <=> m1_subset_1(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    v1_xboole_0(sK1) | (~spl2_2 | spl2_5)),
% 0.21/0.42    inference(subsumption_resolution,[],[f73,f38])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ~r2_hidden(sK0,sK1) | v1_xboole_0(sK1) | spl2_5),
% 0.21/0.42    inference(resolution,[],[f57,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ~m1_subset_1(sK0,sK1) | spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f55])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ~spl2_5 | spl2_6 | spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f53,f31,f59,f55])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl2_1 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    k1_xboole_0 = sK1 | ~m1_subset_1(sK0,sK1) | spl2_1),
% 0.21/0.42    inference(resolution,[],[f23,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f31])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f31])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (13718)------------------------------
% 0.21/0.42  % (13718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (13718)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (13718)Memory used [KB]: 10746
% 0.21/0.42  % (13718)Time elapsed: 0.010 s
% 0.21/0.42  % (13718)------------------------------
% 0.21/0.42  % (13718)------------------------------
% 0.21/0.42  % (13716)Success in time 0.068 s
%------------------------------------------------------------------------------
