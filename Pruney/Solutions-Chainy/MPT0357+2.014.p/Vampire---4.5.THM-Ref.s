%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  72 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 201 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f50,f53,f61])).

fof(f61,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f59,f13])).

fof(f13,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f59,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58,f19])).

fof(f19,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f17,f12])).

fof(f12,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f58,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f49,f14])).

fof(f14,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,
    ( ! [X1] :
        ( r1_tarski(X1,sK1)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_4
  <=> ! [X1] :
        ( r1_tarski(X1,sK1)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f51,f15])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_3 ),
    inference(resolution,[],[f46,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f46,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f28,f48,f44])).

fof(f28,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1))
      | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f18,f20])).

fof(f20,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f17,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f37,f12])).

fof(f37,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(resolution,[],[f32,f16])).

fof(f32,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 18:13:17 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.41  % (24596)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.41  % (24602)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.41  % (24596)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f62,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f39,f50,f53,f61])).
% 0.19/0.41  fof(f61,plain,(
% 0.19/0.41    ~spl3_1 | ~spl3_4),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f60])).
% 0.19/0.41  fof(f60,plain,(
% 0.19/0.41    $false | (~spl3_1 | ~spl3_4)),
% 0.19/0.41    inference(subsumption_resolution,[],[f59,f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,plain,(
% 0.19/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(flattening,[],[f6])).
% 0.19/0.41  fof(f6,plain,(
% 0.19/0.41    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.19/0.41    inference(negated_conjecture,[],[f4])).
% 0.19/0.41  fof(f4,conjecture,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 0.19/0.41  fof(f59,plain,(
% 0.19/0.41    ~r1_tarski(k3_subset_1(sK0,sK1),sK2) | (~spl3_1 | ~spl3_4)),
% 0.19/0.41    inference(forward_demodulation,[],[f58,f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.19/0.41    inference(resolution,[],[f17,f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.19/0.41  fof(f58,plain,(
% 0.19/0.41    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | (~spl3_1 | ~spl3_4)),
% 0.19/0.41    inference(subsumption_resolution,[],[f57,f31])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f30])).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    spl3_1 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.41  fof(f57,plain,(
% 0.19/0.41    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.19/0.41    inference(resolution,[],[f49,f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    ( ! [X1] : (r1_tarski(X1,sK1) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl3_4),
% 0.19/0.41    inference(avatar_component_clause,[],[f48])).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    spl3_4 <=> ! [X1] : (r1_tarski(X1,sK1) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.41  fof(f53,plain,(
% 0.19/0.41    spl3_3),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f52])).
% 0.19/0.41  fof(f52,plain,(
% 0.19/0.41    $false | spl3_3),
% 0.19/0.41    inference(subsumption_resolution,[],[f51,f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f51,plain,(
% 0.19/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_3),
% 0.19/0.41    inference(resolution,[],[f46,f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f8])).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.41  fof(f46,plain,(
% 0.19/0.41    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_3),
% 0.19/0.41    inference(avatar_component_clause,[],[f44])).
% 0.19/0.41  fof(f44,plain,(
% 0.19/0.41    spl3_3 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.41  fof(f50,plain,(
% 0.19/0.41    ~spl3_3 | spl3_4),
% 0.19/0.41    inference(avatar_split_clause,[],[f28,f48,f44])).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    ( ! [X1] : (r1_tarski(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))) )),
% 0.19/0.41    inference(superposition,[],[f18,f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.19/0.41    inference(resolution,[],[f17,f15])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(flattening,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.19/0.41  fof(f39,plain,(
% 0.19/0.41    spl3_1),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f38])).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    $false | spl3_1),
% 0.19/0.41    inference(subsumption_resolution,[],[f37,f12])).
% 0.19/0.41  fof(f37,plain,(
% 0.19/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl3_1),
% 0.19/0.41    inference(resolution,[],[f32,f16])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl3_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f30])).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (24596)------------------------------
% 0.19/0.41  % (24596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (24596)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (24596)Memory used [KB]: 10618
% 0.19/0.41  % (24596)Time elapsed: 0.006 s
% 0.19/0.41  % (24596)------------------------------
% 0.19/0.41  % (24596)------------------------------
% 0.19/0.41  % (24595)Success in time 0.062 s
%------------------------------------------------------------------------------
