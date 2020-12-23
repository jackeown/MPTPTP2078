%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 107 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  141 ( 428 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f804,plain,(
    $false ),
    inference(subsumption_resolution,[],[f793,f25])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f793,plain,(
    r1_tarski(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f776])).

fof(f776,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f35,f761])).

fof(f761,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f760,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f760,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f758,f195])).

fof(f195,plain,(
    ! [X7] : r1_tarski(k6_subset_1(sK0,X7),k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,(
    ! [X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k6_subset_1(sK0,X7),k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f35,f185])).

fof(f185,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f101,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f101,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | k1_xboole_0 = k6_subset_1(X2,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f91,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f91,plain,(
    ! [X10] :
      ( r1_tarski(X10,k1_relat_1(sK2))
      | ~ r1_tarski(X10,sK0) ) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f758,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f757])).

fof(f757,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f28,f731])).

fof(f731,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f374,f38])).

fof(f38,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f374,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f373,f20])).

fof(f373,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f372,f21])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f372,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (29671)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.42  % (29666)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.43  % (29666)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f804,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f793,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ~r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 0.21/0.44  fof(f793,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f776])).
% 0.21/0.44  fof(f776,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(superposition,[],[f35,f761])).
% 0.21/0.44  fof(f761,plain,(
% 0.21/0.44    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f760,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f760,plain,(
% 0.21/0.44    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f758,f195])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    ( ! [X7] : (r1_tarski(k6_subset_1(sK0,X7),k1_relat_1(sK2))) )),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f192])).
% 0.21/0.44  fof(f192,plain,(
% 0.21/0.44    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k6_subset_1(sK0,X7),k1_relat_1(sK2))) )),
% 0.21/0.44    inference(superposition,[],[f35,f185])).
% 0.21/0.44  fof(f185,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2))) )),
% 0.21/0.44    inference(resolution,[],[f101,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f26,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_xboole_0 = k6_subset_1(X2,k1_relat_1(sK2))) )),
% 0.21/0.44    inference(resolution,[],[f91,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f30,f27])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ( ! [X10] : (r1_tarski(X10,k1_relat_1(sK2)) | ~r1_tarski(X10,sK0)) )),
% 0.21/0.44    inference(resolution,[],[f32,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.44  fof(f758,plain,(
% 0.21/0.44    ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f757])).
% 0.21/0.44  fof(f757,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2)),
% 0.21/0.44    inference(superposition,[],[f28,f731])).
% 0.21/0.44  fof(f731,plain,(
% 0.21/0.44    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.21/0.44    inference(superposition,[],[f374,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.44    inference(resolution,[],[f34,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f374,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f373,f20])).
% 0.21/0.44  fof(f373,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f372,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f372,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(resolution,[],[f31,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    v2_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f29,f27])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29666)------------------------------
% 0.21/0.44  % (29666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29666)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29666)Memory used [KB]: 11001
% 0.21/0.44  % (29666)Time elapsed: 0.018 s
% 0.21/0.44  % (29666)------------------------------
% 0.21/0.44  % (29666)------------------------------
% 0.21/0.44  % (29656)Success in time 0.083 s
%------------------------------------------------------------------------------
