%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :  181 ( 303 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f58,f70,f88,f106,f111,f121,f143,f146])).

fof(f146,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | spl3_23 ),
    inference(subsumption_resolution,[],[f144,f41])).

fof(f41,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f144,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl3_6
    | spl3_23 ),
    inference(resolution,[],[f142,f49])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f142,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_23
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f143,plain,
    ( ~ spl3_23
    | spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f138,f119,f101,f140])).

fof(f101,plain,
    ( spl3_16
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f119,plain,
    ( spl3_19
  <=> ! [X2] : k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f138,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_16
    | ~ spl3_19 ),
    inference(superposition,[],[f103,f120])).

fof(f120,plain,
    ( ! [X2] : k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f103,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f121,plain,
    ( spl3_19
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f113,f109,f44,f119])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f109,plain,
    ( spl3_17
  <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f113,plain,
    ( ! [X2] : k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2))
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f110,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f110,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f107,f86,f52,f30,f109])).

fof(f30,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f86,plain,
    ( spl3_13
  <=> ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f107,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f99,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) )
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(superposition,[],[f53,f87])).

fof(f87,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f53,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f106,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f105,f86,f67,f25,f101])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_10
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_1
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f98,f69])).

fof(f69,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f98,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | spl3_1
    | ~ spl3_13 ),
    inference(superposition,[],[f27,f87])).

fof(f27,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f88,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f82,f56,f30,f86])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f57,f32])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f70,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f60,f44,f35,f67])).

fof(f35,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f45,f37])).

fof(f37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (15824)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (15827)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (15824)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f58,f70,f88,f106,f111,f121,f143,f146])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    ~spl3_4 | ~spl3_6 | spl3_23),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    $false | (~spl3_4 | ~spl3_6 | spl3_23)),
% 0.21/0.43    inference(subsumption_resolution,[],[f144,f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (~spl3_6 | spl3_23)),
% 0.21/0.43    inference(resolution,[],[f142,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | spl3_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f140])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    spl3_23 <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.43  fof(f143,plain,(
% 0.21/0.43    ~spl3_23 | spl3_16 | ~spl3_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f138,f119,f101,f140])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    spl3_16 <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    spl3_19 <=> ! [X2] : k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | (spl3_16 | ~spl3_19)),
% 0.21/0.43    inference(superposition,[],[f103,f120])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    ( ! [X2] : (k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2))) ) | ~spl3_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f119])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) | spl3_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f101])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    spl3_19 | ~spl3_5 | ~spl3_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f113,f109,f44,f119])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_5 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    spl3_17 <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X2] : (k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2))) ) | (~spl3_5 | ~spl3_17)),
% 0.21/0.43    inference(resolution,[],[f110,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))) ) | ~spl3_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f109])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    spl3_17 | ~spl3_2 | ~spl3_7 | ~spl3_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f107,f86,f52,f30,f109])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl3_7 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl3_13 <=> ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))) ) | (~spl3_2 | ~spl3_7 | ~spl3_13)),
% 0.21/0.43    inference(subsumption_resolution,[],[f99,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))) ) | (~spl3_7 | ~spl3_13)),
% 0.21/0.43    inference(superposition,[],[f53,f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f86])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f52])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ~spl3_16 | spl3_1 | ~spl3_10 | ~spl3_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f105,f86,f67,f25,f101])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl3_10 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) | (spl3_1 | ~spl3_10 | ~spl3_13)),
% 0.21/0.43    inference(forward_demodulation,[],[f98,f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) | (spl3_1 | ~spl3_13)),
% 0.21/0.43    inference(superposition,[],[f27,f87])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl3_13 | ~spl3_2 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f82,f56,f30,f86])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) ) | (~spl3_2 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f57,f32])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f56])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl3_10 | ~spl3_3 | ~spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f60,f44,f35,f67])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_5)),
% 0.21/0.43    inference(resolution,[],[f45,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f56])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f52])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f48])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f40])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f25])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (15824)------------------------------
% 0.21/0.43  % (15824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (15824)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (15824)Memory used [KB]: 10618
% 0.21/0.43  % (15824)Time elapsed: 0.007 s
% 0.21/0.43  % (15824)------------------------------
% 0.21/0.43  % (15824)------------------------------
% 0.21/0.43  % (15817)Success in time 0.065 s
%------------------------------------------------------------------------------
