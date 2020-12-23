%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:10 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 217 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f44,f52,f86,f94])).

fof(f94,plain,
    ( ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f86,plain,
    ( spl3_7
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f82,f49,f34,f84])).

fof(f49,plain,
    ( spl3_4
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f78,f51])).

fof(f51,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( ! [X0] :
        ( sK0 = k2_xboole_0(sK1,sK0)
        | ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f77,f36])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | k2_xboole_0(X0,X2) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f76,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X0,X2) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X0,X2) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f63,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f63,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK2(X3,X4,X2),X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k2_xboole_0(X4,X2) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X1,X2,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k2_xboole_0(X2,X0) = X0 ) ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,
    ( ~ spl3_4
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f47,f41,f34,f49])).

fof(f41,plain,
    ( spl3_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f47,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f46,f36])).

fof(f46,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f45,f38])).

fof(f45,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_3 ),
    inference(superposition,[],[f43,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f43,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f44,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f39,f29,f41])).

fof(f29,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f31,f19])).

fof(f31,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (11626)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.13/0.41  % (11632)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.13/0.41  % (11626)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f95,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(avatar_sat_refutation,[],[f32,f37,f44,f52,f86,f94])).
% 0.13/0.41  fof(f94,plain,(
% 0.13/0.41    ~spl3_2 | ~spl3_7),
% 0.13/0.41    inference(avatar_contradiction_clause,[],[f93])).
% 0.13/0.41  fof(f93,plain,(
% 0.13/0.41    $false | (~spl3_2 | ~spl3_7)),
% 0.13/0.41    inference(subsumption_resolution,[],[f92,f36])).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.13/0.41    inference(avatar_component_clause,[],[f34])).
% 0.13/0.41  fof(f34,plain,(
% 0.13/0.41    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.13/0.41  fof(f92,plain,(
% 0.13/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_7),
% 0.13/0.41    inference(resolution,[],[f85,f38])).
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(forward_demodulation,[],[f20,f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0] : k2_subset_1(X0) = X0),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.13/0.41  fof(f85,plain,(
% 0.13/0.41    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.13/0.41    inference(avatar_component_clause,[],[f84])).
% 0.13/0.41  fof(f84,plain,(
% 0.13/0.41    spl3_7 <=> ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.13/0.41  fof(f86,plain,(
% 0.13/0.41    spl3_7 | ~spl3_2 | spl3_4),
% 0.13/0.41    inference(avatar_split_clause,[],[f82,f49,f34,f84])).
% 0.13/0.41  fof(f49,plain,(
% 0.13/0.41    spl3_4 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.13/0.41  fof(f82,plain,(
% 0.13/0.41    ( ! [X0] : (~m1_subset_1(sK0,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | (~spl3_2 | spl3_4)),
% 0.13/0.41    inference(subsumption_resolution,[],[f78,f51])).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    sK0 != k2_xboole_0(sK1,sK0) | spl3_4),
% 0.13/0.41    inference(avatar_component_clause,[],[f49])).
% 0.13/0.41  fof(f78,plain,(
% 0.13/0.41    ( ! [X0] : (sK0 = k2_xboole_0(sK1,sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl3_2),
% 0.13/0.41    inference(resolution,[],[f77,f36])).
% 0.13/0.41  fof(f77,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_xboole_0(X0,X2) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f76,f22])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.13/0.41  fof(f76,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X2) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r1_tarski(X0,X2)) )),
% 0.13/0.41    inference(duplicate_literal_removal,[],[f74])).
% 0.13/0.41  fof(f74,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X2) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X2)) )),
% 0.13/0.41    inference(resolution,[],[f63,f25])).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(flattening,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f7])).
% 0.13/0.41  fof(f7,axiom,(
% 0.13/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.13/0.41  fof(f63,plain,(
% 0.13/0.41    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK2(X3,X4,X2),X5) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | k2_xboole_0(X4,X2) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X2))) )),
% 0.13/0.41    inference(resolution,[],[f53,f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f12])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.13/0.41  fof(f53,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X1,X2,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | k2_xboole_0(X2,X0) = X0) )),
% 0.13/0.41    inference(resolution,[],[f26,f22])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f52,plain,(
% 0.13/0.41    ~spl3_4 | ~spl3_2 | spl3_3),
% 0.13/0.41    inference(avatar_split_clause,[],[f47,f41,f34,f49])).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    spl3_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.13/0.41  fof(f47,plain,(
% 0.13/0.41    sK0 != k2_xboole_0(sK1,sK0) | (~spl3_2 | spl3_3)),
% 0.13/0.41    inference(subsumption_resolution,[],[f46,f36])).
% 0.13/0.41  fof(f46,plain,(
% 0.13/0.41    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_3),
% 0.13/0.41    inference(subsumption_resolution,[],[f45,f38])).
% 0.13/0.41  fof(f45,plain,(
% 0.13/0.41    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_3),
% 0.13/0.41    inference(superposition,[],[f43,f27])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f16])).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(flattening,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.13/0.41    inference(ennf_transformation,[],[f6])).
% 0.13/0.41  fof(f6,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_3),
% 0.13/0.41    inference(avatar_component_clause,[],[f41])).
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    ~spl3_3 | spl3_1),
% 0.13/0.41    inference(avatar_split_clause,[],[f39,f29,f41])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    spl3_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.13/0.41  fof(f39,plain,(
% 0.13/0.41    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_1),
% 0.13/0.41    inference(forward_demodulation,[],[f31,f19])).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl3_1),
% 0.13/0.41    inference(avatar_component_clause,[],[f29])).
% 0.13/0.41  fof(f37,plain,(
% 0.13/0.41    spl3_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f17,f34])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.41    inference(cnf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f9])).
% 0.13/0.42  fof(f9,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.13/0.42    inference(negated_conjecture,[],[f8])).
% 0.13/0.42  fof(f8,conjecture,(
% 0.13/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    ~spl3_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f18,f29])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.13/0.42    inference(cnf_transformation,[],[f10])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (11626)------------------------------
% 0.13/0.42  % (11626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (11626)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (11626)Memory used [KB]: 10618
% 0.13/0.42  % (11626)Time elapsed: 0.008 s
% 0.13/0.42  % (11626)------------------------------
% 0.13/0.42  % (11626)------------------------------
% 0.13/0.42  % (11624)Success in time 0.065 s
%------------------------------------------------------------------------------
