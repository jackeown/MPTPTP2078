%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 122 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 337 expanded)
%              Number of equality atoms :   13 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f152,f154,f157,f163,f165])).

fof(f165,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f162,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).

fof(f162,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f163,plain,
    ( ~ spl3_1
    | ~ spl3_5
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f158,f147,f139,f160,f135])).

fof(f135,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f139,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f147,plain,
    ( spl3_4
  <=> r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f158,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_4 ),
    inference(resolution,[],[f149,f53])).

fof(f53,plain,(
    ! [X8,X7,X9] :
      ( r1_tarski(k5_relat_1(X7,X8),k5_relat_1(X7,k3_tarski(k2_tarski(X8,X9))))
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f23,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f149,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f157,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f155,f20])).

fof(f155,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f145,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f145,plain,
    ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_3
  <=> v1_relat_1(k6_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f154,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f141,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f152,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f137,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f137,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f150,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f133,f147,f143,f139,f135])).

fof(f133,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f132,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f132,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK2,sK1))))
    | ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f131,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27,f26,f27])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f131,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK2,k6_subset_1(sK1,sK2)))))
    | ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f51,f22])).

fof(f22,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k6_subset_1(X3,k5_relat_1(X0,X1)),k5_relat_1(X0,X2))
      | ~ r1_tarski(X3,k5_relat_1(X0,k3_tarski(k2_tarski(X1,X2))))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f30,f26,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (22940)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (22940)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f150,f152,f154,f157,f163,f165])).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    $false | spl3_5),
% 0.21/0.45    inference(resolution,[],[f162,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ((~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17,f16,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f160])).
% 0.21/0.45  fof(f160,plain,(
% 0.21/0.45    spl3_5 <=> v1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_5 | ~spl3_2 | spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f158,f147,f139,f160,f135])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    spl3_1 <=> v1_relat_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    spl3_2 <=> v1_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    spl3_4 <=> r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f158,plain,(
% 0.21/0.45    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_4),
% 0.21/0.45    inference(resolution,[],[f149,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X8,X7,X9] : (r1_tarski(k5_relat_1(X7,X8),k5_relat_1(X7,k3_tarski(k2_tarski(X8,X9)))) | ~v1_relat_1(X9) | ~v1_relat_1(X8) | ~v1_relat_1(X7)) )),
% 0.21/0.45    inference(superposition,[],[f32,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k5_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f23,f27,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.45  fof(f149,plain,(
% 0.21/0.45    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) | spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f147])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.45  fof(f156,plain,(
% 0.21/0.45    $false | spl3_3),
% 0.21/0.45    inference(resolution,[],[f155,f20])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | spl3_3),
% 0.21/0.45    inference(resolution,[],[f145,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    ~v1_relat_1(k6_subset_1(sK1,sK2)) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f143])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    spl3_3 <=> v1_relat_1(k6_subset_1(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    $false | spl3_2),
% 0.21/0.45    inference(resolution,[],[f141,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ~v1_relat_1(sK2) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f139])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.45  fof(f151,plain,(
% 0.21/0.45    $false | spl3_1),
% 0.21/0.45    inference(resolution,[],[f137,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f135])).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f133,f147,f143,f139,f135])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) | ~v1_relat_1(k6_subset_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(forward_demodulation,[],[f132,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK2,sK1)))) | ~v1_relat_1(k6_subset_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(forward_demodulation,[],[f131,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f28,f27,f26,f27])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k3_tarski(k2_tarski(sK2,k6_subset_1(sK1,sK2))))) | ~v1_relat_1(k6_subset_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(resolution,[],[f51,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_tarski(k6_subset_1(X3,k5_relat_1(X0,X1)),k5_relat_1(X0,X2)) | ~r1_tarski(X3,k5_relat_1(X0,k3_tarski(k2_tarski(X1,X2)))) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(superposition,[],[f35,f31])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f30,f26,f27])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (22940)------------------------------
% 0.21/0.45  % (22940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (22940)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (22940)Memory used [KB]: 6140
% 0.21/0.45  % (22940)Time elapsed: 0.010 s
% 0.21/0.45  % (22940)------------------------------
% 0.21/0.45  % (22940)------------------------------
% 0.21/0.45  % (22935)Success in time 0.095 s
%------------------------------------------------------------------------------
