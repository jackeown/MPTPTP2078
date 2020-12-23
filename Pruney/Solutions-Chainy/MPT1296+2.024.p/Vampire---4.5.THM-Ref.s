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
% DateTime   : Thu Dec  3 13:13:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 116 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 311 expanded)
%              Number of equality atoms :   44 ( 148 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(subsumption_resolution,[],[f212,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f212,plain,(
    ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2(sK1))) ),
    inference(backward_demodulation,[],[f97,f199])).

fof(f199,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f192,f35])).

fof(f35,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(f192,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(superposition,[],[f92,f77])).

fof(f77,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f72,f51])).

fof(f51,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

fof(f50,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f92,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f70,plain,(
    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f97,plain,(
    ~ r1_tarski(k7_setfam_1(sK0,sK1),k3_subset_1(sK0,sK2(sK1))) ),
    inference(unit_resulting_resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f61,plain,(
    r2_hidden(k3_subset_1(sK0,sK2(sK1)),k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f33,f58,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f58,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f48,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f48,plain,(
    r2_hidden(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (26702)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (26710)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (26710)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (26696)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f212,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2(sK1)))),
% 0.21/0.48    inference(backward_demodulation,[],[f97,f199])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f192,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.48    inference(superposition,[],[f92,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.48    inference(forward_demodulation,[],[f72,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f33,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k1_xboole_0 = k7_setfam_1(sK0,sK1) | k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.21/0.48    inference(resolution,[],[f50,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f33,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f70,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f50,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~r1_tarski(k7_setfam_1(sK0,sK1),k3_subset_1(sK0,sK2(sK1)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f61,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    r2_hidden(k3_subset_1(sK0,sK2(sK1)),k7_setfam_1(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f48,f33,f58,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f33,f48,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    r2_hidden(sK2(sK1),sK1)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f34,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26710)------------------------------
% 0.21/0.48  % (26710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26710)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26710)Memory used [KB]: 6268
% 0.21/0.48  % (26710)Time elapsed: 0.062 s
% 0.21/0.48  % (26710)------------------------------
% 0.21/0.48  % (26710)------------------------------
% 0.21/0.48  % (26709)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (26694)Success in time 0.126 s
%------------------------------------------------------------------------------
