%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 417 expanded)
%              Number of leaves         :    7 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 (1974 expanded)
%              Number of equality atoms :  109 (1703 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f106])).

fof(f106,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f102,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f102,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f86,f96])).

fof(f96,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f83,f85])).

fof(f85,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f84,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f22,f43])).

fof(f43,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f41,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f33,f19])).

fof(f19,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f22,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f70,f56])).

fof(f56,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( sK1 != sK1
    | sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f40,f43])).

fof(f40,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f39])).

fof(f39,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f20])).

fof(f20,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f60,f43])).

fof(f60,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k1_xboole_0 = X0
      | k1_tarski(sK0) = X0 ) ),
    inference(resolution,[],[f42,f23])).

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_tarski(sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f31,f19])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f83,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f21,f60])).

fof(f21,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f19,f85])).

fof(f105,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f88,f96])).

fof(f88,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f22,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (8819)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (8826)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (8818)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (8819)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (8810)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.53  % (8811)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f115,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(subsumption_resolution,[],[f105,f106])).
% 1.28/0.53  fof(f106,plain,(
% 1.28/0.53    k1_xboole_0 = k1_tarski(sK0)),
% 1.28/0.53    inference(forward_demodulation,[],[f102,f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.28/0.53  fof(f102,plain,(
% 1.28/0.53    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.28/0.53    inference(backward_demodulation,[],[f86,f96])).
% 1.28/0.53  fof(f96,plain,(
% 1.28/0.53    k1_xboole_0 = sK2),
% 1.28/0.53    inference(subsumption_resolution,[],[f83,f85])).
% 1.28/0.53  fof(f85,plain,(
% 1.28/0.53    k1_xboole_0 = sK1),
% 1.28/0.53    inference(subsumption_resolution,[],[f84,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f49])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f22,f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.28/0.53    inference(resolution,[],[f41,f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.28/0.53    inference(flattening,[],[f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.28/0.53    inference(nnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    r1_tarski(sK1,k1_tarski(sK0))),
% 1.28/0.53    inference(superposition,[],[f33,f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.28/0.53    inference(ennf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.28/0.53    inference(negated_conjecture,[],[f9])).
% 1.28/0.53  fof(f9,conjecture,(
% 1.28/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(subsumption_resolution,[],[f70,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f48])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    sK1 != sK1 | sK1 != sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f40,f43])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 1.28/0.53    inference(inner_rewriting,[],[f39])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 1.28/0.53    inference(inner_rewriting,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f70,plain,(
% 1.28/0.53    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.28/0.53    inference(superposition,[],[f60,f43])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2),
% 1.28/0.53    inference(resolution,[],[f45,f38])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.28/0.53    inference(equality_resolution,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.53    inference(flattening,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.53    inference(nnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | k1_tarski(sK0) = X0) )),
% 1.28/0.53    inference(resolution,[],[f42,f23])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    ( ! [X0] : (r1_tarski(X0,k1_tarski(sK0)) | ~r1_tarski(X0,sK2)) )),
% 1.28/0.53    inference(superposition,[],[f31,f19])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.28/0.53  fof(f83,plain,(
% 1.28/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f71])).
% 1.28/0.53  fof(f71,plain,(
% 1.28/0.53    sK2 != sK2 | k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 1.28/0.53    inference(superposition,[],[f21,f60])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f86,plain,(
% 1.28/0.53    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.28/0.53    inference(backward_demodulation,[],[f19,f85])).
% 1.28/0.53  fof(f105,plain,(
% 1.28/0.53    k1_xboole_0 != k1_tarski(sK0)),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f103])).
% 1.28/0.53  fof(f103,plain,(
% 1.28/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k1_tarski(sK0)),
% 1.28/0.53    inference(backward_demodulation,[],[f88,f96])).
% 1.28/0.53  fof(f88,plain,(
% 1.28/0.53    k1_xboole_0 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.28/0.53    inference(backward_demodulation,[],[f22,f85])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (8819)------------------------------
% 1.28/0.53  % (8819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (8819)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (8819)Memory used [KB]: 1791
% 1.28/0.53  % (8819)Time elapsed: 0.090 s
% 1.28/0.53  % (8819)------------------------------
% 1.28/0.53  % (8819)------------------------------
% 1.28/0.53  % (8804)Success in time 0.167 s
%------------------------------------------------------------------------------
