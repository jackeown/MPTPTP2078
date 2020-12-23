%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 117 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  169 ( 266 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f87,f227,f764,f1121,f1789,f2185,f2186])).

fof(f2186,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK0,sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2185,plain,
    ( spl2_235
    | ~ spl2_2
    | ~ spl2_128 ),
    inference(avatar_split_clause,[],[f2184,f973,f52,f1945])).

fof(f1945,plain,
    ( spl2_235
  <=> k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_235])])).

fof(f52,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f973,plain,
    ( spl2_128
  <=> v1_relat_1(k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f2184,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_128 ),
    inference(forward_demodulation,[],[f2183,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2183,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,sK0))
    | ~ spl2_2
    | ~ spl2_128 ),
    inference(forward_demodulation,[],[f1935,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1935,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_128 ),
    inference(resolution,[],[f974,f496])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f30,f54])).

fof(f54,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f974,plain,
    ( v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ spl2_128 ),
    inference(avatar_component_clause,[],[f973])).

fof(f1789,plain,
    ( ~ spl2_5
    | spl2_128 ),
    inference(avatar_contradiction_clause,[],[f1758])).

fof(f1758,plain,
    ( $false
    | ~ spl2_5
    | spl2_128 ),
    inference(unit_resulting_resolution,[],[f975,f86,f126,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f126,plain,(
    ! [X2,X0,X1] : r1_tarski(k6_subset_1(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(unit_resulting_resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f86,plain,
    ( v1_relat_1(k2_xboole_0(sK0,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_5
  <=> v1_relat_1(k2_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f975,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | spl2_128 ),
    inference(avatar_component_clause,[],[f973])).

fof(f1121,plain,
    ( spl2_39
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f1119,f761,f356])).

fof(f356,plain,
    ( spl2_39
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f761,plain,
    ( spl2_98
  <=> k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f1119,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_98 ),
    inference(superposition,[],[f34,f763])).

fof(f763,plain,
    ( k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f761])).

fof(f764,plain,
    ( spl2_98
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f448,f57,f52,f761])).

fof(f57,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f448,plain,
    ( k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f59,f54,f30])).

fof(f59,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f227,plain,
    ( ~ spl2_21
    | spl2_1 ),
    inference(avatar_split_clause,[],[f221,f47,f223])).

fof(f223,plain,
    ( spl2_21
  <=> r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f47,plain,
    ( spl2_1
  <=> r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f221,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | spl2_1 ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f87,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f80,f57,f84])).

fof(f80,plain,
    ( v1_relat_1(k2_xboole_0(sK0,sK0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f59,f59,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).

fof(f60,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f55,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (24360)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (24360)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f2187,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f50,f55,f60,f87,f227,f764,f1121,f1789,f2185,f2186])).
% 0.21/0.45  fof(f2186,plain,(
% 0.21/0.45    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK0,sK1)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))),
% 0.21/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.45  fof(f2185,plain,(
% 0.21/0.45    spl2_235 | ~spl2_2 | ~spl2_128),
% 0.21/0.45    inference(avatar_split_clause,[],[f2184,f973,f52,f1945])).
% 0.21/0.45  fof(f1945,plain,(
% 0.21/0.45    spl2_235 <=> k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_235])])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f973,plain,(
% 0.21/0.45    spl2_128 <=> v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).
% 0.21/0.45  fof(f2184,plain,(
% 0.21/0.45    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_128)),
% 0.21/0.45    inference(forward_demodulation,[],[f2183,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f2183,plain,(
% 0.21/0.45    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,sK0)) | (~spl2_2 | ~spl2_128)),
% 0.21/0.45    inference(forward_demodulation,[],[f1935,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f37,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.45  fof(f1935,plain,(
% 0.21/0.45    k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) | (~spl2_2 | ~spl2_128)),
% 0.21/0.45    inference(resolution,[],[f974,f496])).
% 0.21/0.45  fof(f496,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0))) ) | ~spl2_2),
% 0.21/0.45    inference(resolution,[],[f30,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f52])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.45  fof(f974,plain,(
% 0.21/0.45    v1_relat_1(k6_subset_1(sK0,sK1)) | ~spl2_128),
% 0.21/0.45    inference(avatar_component_clause,[],[f973])).
% 0.21/0.45  fof(f1789,plain,(
% 0.21/0.45    ~spl2_5 | spl2_128),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1758])).
% 0.21/0.45  fof(f1758,plain,(
% 0.21/0.45    $false | (~spl2_5 | spl2_128)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f975,f86,f126,f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.21/0.45    inference(resolution,[],[f33,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f34,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f41,f35])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    v1_relat_1(k2_xboole_0(sK0,sK0)) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl2_5 <=> v1_relat_1(k2_xboole_0(sK0,sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f975,plain,(
% 0.21/0.45    ~v1_relat_1(k6_subset_1(sK0,sK1)) | spl2_128),
% 0.21/0.45    inference(avatar_component_clause,[],[f973])).
% 0.21/0.45  fof(f1121,plain,(
% 0.21/0.45    spl2_39 | ~spl2_98),
% 0.21/0.45    inference(avatar_split_clause,[],[f1119,f761,f356])).
% 0.21/0.45  fof(f356,plain,(
% 0.21/0.45    spl2_39 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.45  fof(f761,plain,(
% 0.21/0.45    spl2_98 <=> k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 0.21/0.45  fof(f1119,plain,(
% 0.21/0.45    r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) | ~spl2_98),
% 0.21/0.45    inference(superposition,[],[f34,f763])).
% 0.21/0.45  fof(f763,plain,(
% 0.21/0.45    k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl2_98),
% 0.21/0.45    inference(avatar_component_clause,[],[f761])).
% 0.21/0.45  fof(f764,plain,(
% 0.21/0.45    spl2_98 | ~spl2_2 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f448,f57,f52,f761])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl2_3 <=> v1_relat_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f448,plain,(
% 0.21/0.45    k2_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f59,f54,f30])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    v1_relat_1(sK0) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f57])).
% 0.21/0.45  fof(f227,plain,(
% 0.21/0.45    ~spl2_21 | spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f221,f47,f223])).
% 0.21/0.45  fof(f223,plain,(
% 0.21/0.45    spl2_21 <=> r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl2_1 <=> r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) | spl2_1),
% 0.21/0.45    inference(resolution,[],[f45,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f47])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f42,f35])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    spl2_5 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f80,f57,f84])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    v1_relat_1(k2_xboole_0(sK0,sK0)) | ~spl2_3),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f59,f59,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k2_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f12])).
% 0.21/0.45  fof(f12,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f52])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f47])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (24360)------------------------------
% 0.21/0.45  % (24360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (24360)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (24360)Memory used [KB]: 7547
% 0.21/0.45  % (24360)Time elapsed: 0.027 s
% 0.21/0.45  % (24360)------------------------------
% 0.21/0.45  % (24360)------------------------------
% 0.21/0.45  % (24353)Success in time 0.094 s
%------------------------------------------------------------------------------
