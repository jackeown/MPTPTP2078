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
% DateTime   : Thu Dec  3 12:45:03 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 169 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f45,f55])).

fof(f55,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f53,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_4
  <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k2_xboole_0(X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k2_xboole_0(X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_xboole_0(X0,X1),k1_zfmisc_1(X2))
      | r1_tarski(k3_subset_1(X2,k2_xboole_0(X0,X1)),k3_subset_1(X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f45,plain,
    ( ~ spl3_4
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f32,f27,f22,f42])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f39,f24])).

fof(f39,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f36,f34])).

fof(f36,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(superposition,[],[f29,f20])).

fof(f29,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f30,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n019.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.11/0.34  % (5595)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.11/0.34  % (5595)Refutation found. Thanks to Tanya!
% 0.11/0.34  % SZS status Theorem for theBenchmark
% 0.11/0.34  % SZS output start Proof for theBenchmark
% 0.11/0.34  fof(f56,plain,(
% 0.11/0.34    $false),
% 0.11/0.34    inference(avatar_sat_refutation,[],[f25,f30,f35,f45,f55])).
% 0.11/0.34  fof(f55,plain,(
% 0.11/0.34    ~spl3_1 | ~spl3_3 | spl3_4),
% 0.11/0.34    inference(avatar_contradiction_clause,[],[f54])).
% 0.11/0.34  fof(f54,plain,(
% 0.11/0.34    $false | (~spl3_1 | ~spl3_3 | spl3_4)),
% 0.11/0.34    inference(subsumption_resolution,[],[f53,f34])).
% 0.11/0.34  fof(f34,plain,(
% 0.11/0.34    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.11/0.34    inference(avatar_component_clause,[],[f32])).
% 0.11/0.34  fof(f32,plain,(
% 0.11/0.34    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.11/0.34    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.11/0.34  fof(f53,plain,(
% 0.11/0.34    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_1 | spl3_4)),
% 0.11/0.34    inference(subsumption_resolution,[],[f49,f24])).
% 0.11/0.34  fof(f24,plain,(
% 0.11/0.34    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.11/0.34    inference(avatar_component_clause,[],[f22])).
% 0.11/0.34  fof(f22,plain,(
% 0.11/0.34    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.11/0.34    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.11/0.34  fof(f49,plain,(
% 0.11/0.34    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl3_4),
% 0.11/0.34    inference(resolution,[],[f48,f44])).
% 0.11/0.34  fof(f44,plain,(
% 0.11/0.34    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | spl3_4),
% 0.11/0.34    inference(avatar_component_clause,[],[f42])).
% 0.11/0.34  fof(f42,plain,(
% 0.11/0.34    spl3_4 <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.11/0.34    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.11/0.34  fof(f48,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k2_xboole_0(X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(duplicate_literal_removal,[],[f47])).
% 0.11/0.34  fof(f47,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k2_xboole_0(X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(resolution,[],[f46,f38])).
% 0.11/0.34  fof(f38,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(duplicate_literal_removal,[],[f37])).
% 0.11/0.34  fof(f37,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(superposition,[],[f19,f20])).
% 0.11/0.34  fof(f20,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f12])).
% 0.11/0.34  fof(f12,plain,(
% 0.11/0.34    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.34    inference(flattening,[],[f11])).
% 0.11/0.34  fof(f11,plain,(
% 0.11/0.34    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.11/0.34    inference(ennf_transformation,[],[f3])).
% 0.11/0.34  fof(f3,axiom,(
% 0.11/0.34    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.11/0.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.11/0.34  fof(f19,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f10])).
% 0.11/0.34  fof(f10,plain,(
% 0.11/0.34    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.34    inference(flattening,[],[f9])).
% 0.11/0.34  fof(f9,plain,(
% 0.11/0.34    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.11/0.34    inference(ennf_transformation,[],[f2])).
% 0.11/0.34  fof(f2,axiom,(
% 0.11/0.34    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.11/0.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.11/0.34  fof(f46,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (~m1_subset_1(k2_xboole_0(X0,X1),k1_zfmisc_1(X2)) | r1_tarski(k3_subset_1(X2,k2_xboole_0(X0,X1)),k3_subset_1(X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 0.11/0.34    inference(resolution,[],[f18,f16])).
% 0.11/0.34  fof(f16,plain,(
% 0.11/0.34    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f1])).
% 0.11/0.34  fof(f1,axiom,(
% 0.11/0.34    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.11/0.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.11/0.34  fof(f18,plain,(
% 0.11/0.34    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.34    inference(cnf_transformation,[],[f8])).
% 0.11/0.34  fof(f8,plain,(
% 0.11/0.34    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.34    inference(ennf_transformation,[],[f4])).
% 0.11/0.34  fof(f4,axiom,(
% 0.11/0.34    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.11/0.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.11/0.34  fof(f45,plain,(
% 0.11/0.34    ~spl3_4 | ~spl3_1 | spl3_2 | ~spl3_3),
% 0.11/0.34    inference(avatar_split_clause,[],[f40,f32,f27,f22,f42])).
% 0.11/0.34  fof(f27,plain,(
% 0.11/0.34    spl3_2 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.11/0.34    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.11/0.34  fof(f40,plain,(
% 0.11/0.34    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.11/0.34    inference(subsumption_resolution,[],[f39,f24])).
% 0.11/0.34  fof(f39,plain,(
% 0.11/0.34    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl3_2 | ~spl3_3)),
% 0.11/0.34    inference(subsumption_resolution,[],[f36,f34])).
% 0.11/0.34  fof(f36,plain,(
% 0.11/0.34    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_2),
% 0.11/0.34    inference(superposition,[],[f29,f20])).
% 0.11/0.34  fof(f29,plain,(
% 0.11/0.34    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.11/0.34    inference(avatar_component_clause,[],[f27])).
% 0.11/0.34  fof(f35,plain,(
% 0.11/0.34    spl3_3),
% 0.11/0.34    inference(avatar_split_clause,[],[f13,f32])).
% 0.11/0.34  fof(f13,plain,(
% 0.11/0.34    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.11/0.34    inference(cnf_transformation,[],[f7])).
% 0.11/0.34  fof(f7,plain,(
% 0.11/0.34    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.34    inference(ennf_transformation,[],[f6])).
% 0.11/0.34  fof(f6,negated_conjecture,(
% 0.11/0.34    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.11/0.34    inference(negated_conjecture,[],[f5])).
% 0.11/0.34  fof(f5,conjecture,(
% 0.11/0.34    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.11/0.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 0.11/0.34  fof(f30,plain,(
% 0.11/0.34    ~spl3_2),
% 0.11/0.34    inference(avatar_split_clause,[],[f14,f27])).
% 0.11/0.34  fof(f14,plain,(
% 0.11/0.34    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.11/0.34    inference(cnf_transformation,[],[f7])).
% 0.11/0.34  fof(f25,plain,(
% 0.11/0.34    spl3_1),
% 0.11/0.34    inference(avatar_split_clause,[],[f15,f22])).
% 0.11/0.34  fof(f15,plain,(
% 0.11/0.34    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.11/0.34    inference(cnf_transformation,[],[f7])).
% 0.11/0.34  % SZS output end Proof for theBenchmark
% 0.11/0.34  % (5595)------------------------------
% 0.11/0.34  % (5595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.34  % (5595)Termination reason: Refutation
% 0.11/0.34  
% 0.11/0.34  % (5595)Memory used [KB]: 10618
% 0.11/0.34  % (5595)Time elapsed: 0.005 s
% 0.11/0.34  % (5595)------------------------------
% 0.11/0.34  % (5595)------------------------------
% 0.11/0.34  % (5599)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.11/0.35  % (5593)Success in time 0.067 s
%------------------------------------------------------------------------------
