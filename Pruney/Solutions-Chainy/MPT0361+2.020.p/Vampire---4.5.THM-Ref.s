%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 ( 214 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f53,f90,f99,f117,f122])).

fof(f122,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl3_11 ),
    inference(subsumption_resolution,[],[f119,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f119,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_11 ),
    inference(resolution,[],[f116,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f116,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_11
  <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f117,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | ~ spl3_3
    | spl3_9 ),
    inference(avatar_split_clause,[],[f112,f96,f39,f29,f114])).

fof(f29,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f96,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f112,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f31,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f111,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f110,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_9 ),
    inference(superposition,[],[f98,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f98,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( ~ spl3_9
    | spl3_8 ),
    inference(avatar_split_clause,[],[f93,f87,f96])).

fof(f87,plain,
    ( spl3_8
  <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | spl3_8 ),
    inference(resolution,[],[f89,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f89,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f90,plain,
    ( ~ spl3_8
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f85,f50,f39,f34,f29,f87])).

fof(f34,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_4
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f84,f52])).

fof(f52,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f84,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f83,f41])).

fof(f83,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(superposition,[],[f36,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_subset_1(X1,X2,X0)) = k3_subset_1(X1,k4_subset_1(X1,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f26,f23])).

fof(f23,plain,(
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

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f36,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f53,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f47,f29,f50])).

fof(f47,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f23,f31])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f37,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (10513)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  % (10513)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f128,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f32,f37,f42,f53,f90,f99,f117,f122])).
% 0.20/0.41  fof(f122,plain,(
% 0.20/0.41    spl3_11),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.41  fof(f121,plain,(
% 0.20/0.41    $false | spl3_11),
% 0.20/0.41    inference(subsumption_resolution,[],[f119,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl3_11),
% 0.20/0.41    inference(resolution,[],[f116,f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 0.20/0.41    inference(superposition,[],[f25,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.41  fof(f116,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl3_11),
% 0.20/0.41    inference(avatar_component_clause,[],[f114])).
% 0.20/0.41  fof(f114,plain,(
% 0.20/0.41    spl3_11 <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.41  fof(f117,plain,(
% 0.20/0.41    ~spl3_11 | ~spl3_1 | ~spl3_3 | spl3_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f112,f96,f39,f29,f114])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.41  fof(f96,plain,(
% 0.20/0.41    spl3_9 <=> r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_3 | spl3_9)),
% 0.20/0.41    inference(subsumption_resolution,[],[f111,f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f29])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_3 | spl3_9)),
% 0.20/0.41    inference(subsumption_resolution,[],[f110,f41])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f39])).
% 0.20/0.41  fof(f110,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_9),
% 0.20/0.41    inference(superposition,[],[f98,f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(flattening,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.41  fof(f98,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | spl3_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f96])).
% 0.20/0.41  fof(f99,plain,(
% 0.20/0.41    ~spl3_9 | spl3_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f93,f87,f96])).
% 0.20/0.41  fof(f87,plain,(
% 0.20/0.41    spl3_8 <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.41  fof(f93,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | spl3_8),
% 0.20/0.41    inference(resolution,[],[f89,f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl3_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f87])).
% 0.20/0.41  fof(f90,plain,(
% 0.20/0.41    ~spl3_8 | ~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f85,f50,f39,f34,f29,f87])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    spl3_2 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    spl3_4 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.20/0.41    inference(forward_demodulation,[],[f84,f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f50])).
% 0.20/0.41  fof(f84,plain,(
% 0.20/0.41    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.20/0.41    inference(subsumption_resolution,[],[f83,f41])).
% 0.20/0.41  fof(f83,plain,(
% 0.20/0.41    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_1 | spl3_2)),
% 0.20/0.41    inference(subsumption_resolution,[],[f81,f31])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl3_2),
% 0.20/0.41    inference(superposition,[],[f36,f59])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_subset_1(X1,X2,X0)) = k3_subset_1(X1,k4_subset_1(X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.41    inference(resolution,[],[f26,f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(flattening,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f34])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    spl3_4 | ~spl3_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f47,f29,f50])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.20/0.41    inference(resolution,[],[f23,f31])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    spl3_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f18,f39])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.20/0.41    inference(negated_conjecture,[],[f8])).
% 0.20/0.41  fof(f8,conjecture,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ~spl3_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f19,f34])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    spl3_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f20,f29])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (10513)------------------------------
% 0.20/0.41  % (10513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (10513)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (10513)Memory used [KB]: 10618
% 0.20/0.41  % (10513)Time elapsed: 0.032 s
% 0.20/0.41  % (10513)------------------------------
% 0.20/0.41  % (10513)------------------------------
% 0.20/0.42  % (10511)Success in time 0.062 s
%------------------------------------------------------------------------------
