%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 198 expanded)
%              Number of leaves         :   15 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 366 expanded)
%              Number of equality atoms :   15 (  99 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f219,f228,f238])).

fof(f238,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f234,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f234,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(resolution,[],[f232,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f232,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f231,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f231,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f230,f64])).

fof(f64,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(forward_demodulation,[],[f59,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f59,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X2)),X2) ),
    inference(superposition,[],[f28,f51])).

fof(f51,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4)) ),
    inference(superposition,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f29,f38,f38])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f230,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f218,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f218,plain,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f228,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f224,f23])).

fof(f224,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(resolution,[],[f222,f48])).

fof(f222,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f221,f23])).

fof(f221,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f220,f28])).

fof(f220,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(resolution,[],[f214,f26])).

fof(f214,plain,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f219,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f123,f216,f212])).

fof(f123,plain,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f44,plain,(
    ~ r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f43,f41])).

fof(f43,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f39,f41])).

fof(f39,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f25,f38,f38])).

fof(f25,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:40:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.44  % (14896)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.45  % (14896)Refutation found. Thanks to Tanya!
% 0.23/0.45  % SZS status Theorem for theBenchmark
% 0.23/0.45  % SZS output start Proof for theBenchmark
% 0.23/0.45  fof(f239,plain,(
% 0.23/0.45    $false),
% 0.23/0.45    inference(avatar_sat_refutation,[],[f219,f228,f238])).
% 0.23/0.45  fof(f238,plain,(
% 0.23/0.45    spl2_2),
% 0.23/0.45    inference(avatar_contradiction_clause,[],[f237])).
% 0.23/0.45  fof(f237,plain,(
% 0.23/0.45    $false | spl2_2),
% 0.23/0.45    inference(subsumption_resolution,[],[f234,f23])).
% 0.23/0.45  fof(f23,plain,(
% 0.23/0.45    v1_relat_1(sK0)),
% 0.23/0.45    inference(cnf_transformation,[],[f21])).
% 0.23/0.45  fof(f21,plain,(
% 0.23/0.45    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.23/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20,f19])).
% 0.23/0.45  fof(f19,plain,(
% 0.23/0.45    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f20,plain,(
% 0.23/0.45    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f13,plain,(
% 0.23/0.45    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f12])).
% 0.23/0.45  fof(f12,negated_conjecture,(
% 0.23/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.45    inference(negated_conjecture,[],[f11])).
% 0.23/0.45  fof(f11,conjecture,(
% 0.23/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 0.23/0.45  fof(f234,plain,(
% 0.23/0.45    ~v1_relat_1(sK0) | spl2_2),
% 0.23/0.45    inference(resolution,[],[f232,f48])).
% 0.23/0.45  fof(f48,plain,(
% 0.23/0.45    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.23/0.45    inference(resolution,[],[f47,f28])).
% 0.23/0.45  fof(f28,plain,(
% 0.23/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f3])).
% 0.23/0.45  fof(f3,axiom,(
% 0.23/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.45  fof(f47,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.23/0.45    inference(resolution,[],[f27,f34])).
% 0.23/0.45  fof(f34,plain,(
% 0.23/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f22])).
% 0.23/0.45  fof(f22,plain,(
% 0.23/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.45    inference(nnf_transformation,[],[f8])).
% 0.23/0.45  fof(f8,axiom,(
% 0.23/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.45  fof(f27,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f16])).
% 0.23/0.45  fof(f16,plain,(
% 0.23/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f9])).
% 0.23/0.45  fof(f9,axiom,(
% 0.23/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.45  fof(f232,plain,(
% 0.23/0.45    ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_2),
% 0.23/0.45    inference(subsumption_resolution,[],[f231,f24])).
% 0.23/0.45  fof(f24,plain,(
% 0.23/0.45    v1_relat_1(sK1)),
% 0.23/0.45    inference(cnf_transformation,[],[f21])).
% 0.23/0.45  fof(f231,plain,(
% 0.23/0.45    ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_2),
% 0.23/0.45    inference(subsumption_resolution,[],[f230,f64])).
% 0.23/0.45  fof(f64,plain,(
% 0.23/0.45    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 0.23/0.45    inference(forward_demodulation,[],[f59,f41])).
% 0.23/0.45  fof(f41,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.45    inference(definition_unfolding,[],[f32,f38])).
% 0.23/0.45  fof(f38,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.45    inference(definition_unfolding,[],[f30,f37])).
% 0.23/0.45  fof(f37,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.45    inference(definition_unfolding,[],[f31,f35])).
% 0.23/0.45  fof(f35,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f6])).
% 0.23/0.45  fof(f6,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.45  fof(f31,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f5])).
% 0.23/0.45  fof(f5,axiom,(
% 0.23/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.45  fof(f30,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f7])).
% 0.23/0.45  fof(f7,axiom,(
% 0.23/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.45  fof(f32,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f4])).
% 0.23/0.45  fof(f4,axiom,(
% 0.23/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.45  fof(f59,plain,(
% 0.23/0.45    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X2)),X2)) )),
% 0.23/0.45    inference(superposition,[],[f28,f51])).
% 0.23/0.45  fof(f51,plain,(
% 0.23/0.45    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) )),
% 0.23/0.45    inference(superposition,[],[f40,f41])).
% 0.23/0.45  fof(f40,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.23/0.45    inference(definition_unfolding,[],[f29,f38,f38])).
% 0.23/0.45  fof(f29,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f1])).
% 0.23/0.45  fof(f1,axiom,(
% 0.23/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.45  fof(f230,plain,(
% 0.23/0.45    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_2),
% 0.23/0.45    inference(resolution,[],[f218,f26])).
% 0.23/0.45  fof(f26,plain,(
% 0.23/0.45    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f15])).
% 0.23/0.45  fof(f15,plain,(
% 0.23/0.45    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.45    inference(flattening,[],[f14])).
% 0.23/0.45  fof(f14,plain,(
% 0.23/0.45    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.45    inference(ennf_transformation,[],[f10])).
% 0.23/0.45  fof(f10,axiom,(
% 0.23/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.23/0.45  fof(f218,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1)) | spl2_2),
% 0.23/0.45    inference(avatar_component_clause,[],[f216])).
% 0.23/0.45  fof(f216,plain,(
% 0.23/0.45    spl2_2 <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.45  fof(f228,plain,(
% 0.23/0.45    spl2_1),
% 0.23/0.45    inference(avatar_contradiction_clause,[],[f227])).
% 0.23/0.45  fof(f227,plain,(
% 0.23/0.45    $false | spl2_1),
% 0.23/0.45    inference(subsumption_resolution,[],[f224,f23])).
% 0.23/0.45  fof(f224,plain,(
% 0.23/0.45    ~v1_relat_1(sK0) | spl2_1),
% 0.23/0.45    inference(resolution,[],[f222,f48])).
% 0.23/0.45  fof(f222,plain,(
% 0.23/0.45    ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.23/0.45    inference(subsumption_resolution,[],[f221,f23])).
% 0.23/0.45  fof(f221,plain,(
% 0.23/0.45    ~v1_relat_1(sK0) | ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.23/0.45    inference(subsumption_resolution,[],[f220,f28])).
% 0.23/0.45  fof(f220,plain,(
% 0.23/0.45    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.23/0.45    inference(resolution,[],[f214,f26])).
% 0.23/0.45  fof(f214,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK0)) | spl2_1),
% 0.23/0.45    inference(avatar_component_clause,[],[f212])).
% 0.23/0.45  fof(f212,plain,(
% 0.23/0.45    spl2_1 <=> r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK0))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.45  fof(f219,plain,(
% 0.23/0.45    ~spl2_1 | ~spl2_2),
% 0.23/0.45    inference(avatar_split_clause,[],[f123,f216,f212])).
% 0.23/0.45  fof(f123,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_relat_1(sK0))),
% 0.23/0.45    inference(resolution,[],[f44,f45])).
% 0.23/0.45  fof(f45,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.45    inference(forward_demodulation,[],[f42,f41])).
% 0.23/0.45  fof(f42,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.45    inference(definition_unfolding,[],[f36,f38])).
% 0.23/0.45  fof(f36,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f18])).
% 0.23/0.45  fof(f18,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.45    inference(flattening,[],[f17])).
% 0.23/0.45  fof(f17,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.45    inference(ennf_transformation,[],[f2])).
% 0.23/0.45  fof(f2,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.23/0.45  fof(f44,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.23/0.45    inference(forward_demodulation,[],[f43,f41])).
% 0.23/0.45  fof(f43,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k3_relat_1(sK0),k4_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.23/0.45    inference(backward_demodulation,[],[f39,f41])).
% 0.23/0.45  fof(f39,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.23/0.45    inference(definition_unfolding,[],[f25,f38,f38])).
% 0.23/0.45  fof(f25,plain,(
% 0.23/0.45    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.23/0.45    inference(cnf_transformation,[],[f21])).
% 0.23/0.45  % SZS output end Proof for theBenchmark
% 0.23/0.45  % (14896)------------------------------
% 0.23/0.45  % (14896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.45  % (14896)Termination reason: Refutation
% 0.23/0.45  
% 0.23/0.45  % (14896)Memory used [KB]: 10746
% 0.23/0.45  % (14896)Time elapsed: 0.034 s
% 0.23/0.45  % (14896)------------------------------
% 0.23/0.45  % (14896)------------------------------
% 0.23/0.45  % (14886)Success in time 0.085 s
%------------------------------------------------------------------------------
