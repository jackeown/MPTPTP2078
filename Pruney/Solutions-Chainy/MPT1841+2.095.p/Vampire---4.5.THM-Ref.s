%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 128 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   19
%              Number of atoms          :  170 ( 370 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f113,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f113,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f112,f40])).

fof(f112,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f111,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f60,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = sK2(X0) ),
    inference(resolution,[],[f62,f45])).

fof(f45,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f60,plain,(
    ! [X0] : r1_tarski(sK2(X0),X0) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f58,f107])).

fof(f107,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f96,f35])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f96,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f83,f88])).

fof(f88,plain,(
    k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f86,f35])).

fof(f86,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f84,f62])).

fof(f84,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f79,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f76,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f76,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f75,f37])).

fof(f37,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f83,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f59,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f46,f56,f57])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (21084)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.42  % (21084)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f114])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0),
% 0.21/0.42    inference(superposition,[],[f113,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    inference(forward_demodulation,[],[f112,f40])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.21/0.42    inference(superposition,[],[f111,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(resolution,[],[f50,f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(backward_demodulation,[],[f60,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = sK2(X0)) )),
% 0.21/0.42    inference(resolution,[],[f62,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(sK2(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,axiom,(
% 0.21/0.42    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(resolution,[],[f55,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(sK2(X0),X0)) )),
% 0.21/0.42    inference(resolution,[],[f53,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f33])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.42    inference(nnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) )),
% 0.21/0.42    inference(superposition,[],[f58,f107])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.42    inference(resolution,[],[f96,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~v1_xboole_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f16])).
% 0.21/0.42  fof(f16,conjecture,(
% 0.21/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    v1_xboole_0(sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.42    inference(backward_demodulation,[],[f83,f88])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.21/0.42    inference(resolution,[],[f86,f35])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    v1_xboole_0(sK0) | k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.21/0.42    inference(resolution,[],[f84,f62])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f79,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    m1_subset_1(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f76,f52])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,axiom,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f75,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | v1_xboole_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f43,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    v1_zfmisc_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,axiom,(
% 0.21/0.42    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | v1_xboole_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f59,f36])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f51,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f41,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,axiom,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0))))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f46,f56,f57])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f48,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,axiom,(
% 0.21/0.42    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (21084)------------------------------
% 0.21/0.42  % (21084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21084)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (21084)Memory used [KB]: 1663
% 0.21/0.42  % (21084)Time elapsed: 0.004 s
% 0.21/0.42  % (21084)------------------------------
% 0.21/0.42  % (21084)------------------------------
% 0.21/0.42  % (21082)Success in time 0.058 s
%------------------------------------------------------------------------------
