%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 141 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 ( 391 expanded)
%              Number of equality atoms :   55 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f205,f252])).

fof(f252,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f94,f250])).

fof(f250,plain,(
    k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f241,f61])).

fof(f61,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f241,plain,
    ( v1_subset_1(sK0,sK0)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(superposition,[],[f37,f238])).

fof(f238,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(superposition,[],[f87,f229])).

fof(f229,plain,(
    k6_domain_1(sK0,sK1) = k3_xboole_0(sK0,k6_domain_1(sK0,sK1)) ),
    inference(resolution,[],[f223,f35])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f223,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k3_xboole_0(sK0,k6_domain_1(sK0,sK1)) ),
    inference(resolution,[],[f86,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k3_xboole_0(X0,k6_domain_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f84,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k3_xboole_0(k6_domain_1(X0,X1),X0) ) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f87,plain,(
    ! [X0] :
      ( sK0 = k3_xboole_0(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f77,f35])).

fof(f77,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0)
      | sK0 = k3_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | v1_xboole_0(sK0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(k3_xboole_0(sK0,X0))
      | r1_tarski(sK0,X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f37,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f89,f35])).

fof(f89,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f60,f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f205,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f115,f62])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f58,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) ),
    inference(superposition,[],[f59,f45])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f46,f56,f57])).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (29669)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.44  % (29675)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.44  % (29669)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f270,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f266])).
% 0.20/0.44  fof(f266,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0),
% 0.20/0.44    inference(superposition,[],[f205,f252])).
% 0.20/0.44  fof(f252,plain,(
% 0.20/0.44    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.44    inference(backward_demodulation,[],[f94,f250])).
% 0.20/0.44  fof(f250,plain,(
% 0.20/0.44    k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.20/0.44    inference(resolution,[],[f241,f61])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.20/0.44    inference(backward_demodulation,[],[f39,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.20/0.44  fof(f241,plain,(
% 0.20/0.44    v1_subset_1(sK0,sK0) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.20/0.44    inference(superposition,[],[f37,f238])).
% 0.20/0.44  fof(f238,plain,(
% 0.20/0.44    sK0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.20/0.44    inference(superposition,[],[f87,f229])).
% 0.20/0.44  fof(f229,plain,(
% 0.20/0.44    k6_domain_1(sK0,sK1) = k3_xboole_0(sK0,k6_domain_1(sK0,sK1))),
% 0.20/0.44    inference(resolution,[],[f223,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ~v1_xboole_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.44    inference(negated_conjecture,[],[f17])).
% 0.20/0.44  fof(f17,conjecture,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.44  fof(f223,plain,(
% 0.20/0.44    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k3_xboole_0(sK0,k6_domain_1(sK0,sK1))),
% 0.20/0.44    inference(resolution,[],[f86,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    m1_subset_1(sK1,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k3_xboole_0(X0,k6_domain_1(X0,X1))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f84,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k3_xboole_0(k6_domain_1(X0,X1),X0)) )),
% 0.20/0.44    inference(resolution,[],[f79,f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.44    inference(resolution,[],[f53,f54])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.44    inference(nnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    ( ! [X0] : (sK0 = k3_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 0.20/0.44    inference(resolution,[],[f77,f35])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(sK0) | k1_xboole_0 = k3_xboole_0(sK0,X0) | sK0 = k3_xboole_0(sK0,X0)) )),
% 0.20/0.44    inference(resolution,[],[f64,f51])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(sK0,X0) | v1_xboole_0(sK0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 0.20/0.44    inference(resolution,[],[f63,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k3_xboole_0(sK0,X0)) | r1_tarski(sK0,X0) | v1_xboole_0(sK0)) )),
% 0.20/0.44    inference(resolution,[],[f43,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    v1_zfmisc_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(k3_xboole_0(X0,X1)) | r1_tarski(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,axiom,(
% 0.20/0.44    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f33])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.44    inference(resolution,[],[f89,f35])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.44    inference(resolution,[],[f60,f36])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f52,f57])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f41,f48])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.44  fof(f205,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.20/0.44    inference(superposition,[],[f115,f62])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 0.20/0.44    inference(backward_demodulation,[],[f58,f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.44    inference(rectify,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f44,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f50,f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.44    inference(rectify,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.44    inference(superposition,[],[f59,f45])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0))))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f46,f56,f57])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (29669)------------------------------
% 0.20/0.44  % (29669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (29669)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (29669)Memory used [KB]: 1791
% 0.20/0.44  % (29669)Time elapsed: 0.035 s
% 0.20/0.44  % (29669)------------------------------
% 0.20/0.44  % (29669)------------------------------
% 0.20/0.44  % (29667)Success in time 0.087 s
%------------------------------------------------------------------------------
