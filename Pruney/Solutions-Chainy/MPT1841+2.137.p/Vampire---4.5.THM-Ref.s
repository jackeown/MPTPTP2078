%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:27 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 187 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 ( 716 expanded)
%              Number of equality atoms :   62 ( 103 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f131,f53])).

fof(f53,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f32,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f131,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f72,f126])).

fof(f126,plain,(
    sK0 = k2_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f69,f121])).

fof(f121,plain,(
    sK0 = k6_domain_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f61,f110])).

fof(f110,plain,(
    sK1 = sK2(sK0) ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f54,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f81,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK2(sK0) = X1 ) ),
    inference(superposition,[],[f51,f79])).

fof(f79,plain,(
    sK0 = k2_tarski(sK2(sK0),sK2(sK0)) ),
    inference(forward_demodulation,[],[f78,f61])).

fof(f78,plain,(
    k6_domain_1(sK0,sK2(sK0)) = k2_tarski(sK2(sK0),sK2(sK0)) ),
    inference(subsumption_resolution,[],[f77,f28])).

fof(f77,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK2(sK0)) = k2_tarski(sK2(sK0),sK2(sK0)) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f51,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (28175)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f61,plain,(
    sK0 = k6_domain_1(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f60,f28])).

fof(f60,plain,
    ( sK0 = k6_domain_1(sK0,sK2(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f66,f28])).

fof(f66,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f44,f29])).

fof(f72,plain,(
    v1_subset_1(k2_tarski(sK1,sK1),sK0) ),
    inference(backward_demodulation,[],[f30,f69])).

fof(f30,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (28184)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (28176)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (28184)Refutation not found, incomplete strategy% (28184)------------------------------
% 0.21/0.55  % (28184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (28184)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (28184)Memory used [KB]: 1791
% 1.32/0.55  % (28184)Time elapsed: 0.118 s
% 1.32/0.55  % (28184)------------------------------
% 1.32/0.55  % (28184)------------------------------
% 1.32/0.56  % (28176)Refutation found. Thanks to Tanya!
% 1.32/0.56  % SZS status Theorem for theBenchmark
% 1.32/0.56  % SZS output start Proof for theBenchmark
% 1.32/0.56  fof(f136,plain,(
% 1.32/0.56    $false),
% 1.32/0.56    inference(subsumption_resolution,[],[f131,f53])).
% 1.32/0.56  fof(f53,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.32/0.56    inference(backward_demodulation,[],[f32,f33])).
% 1.32/0.56  fof(f33,plain,(
% 1.32/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.32/0.56    inference(cnf_transformation,[],[f3])).
% 1.32/0.56  fof(f3,axiom,(
% 1.32/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.32/0.56  fof(f32,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f4])).
% 1.32/0.56  fof(f4,axiom,(
% 1.32/0.56    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.32/0.56  fof(f131,plain,(
% 1.32/0.56    v1_subset_1(sK0,sK0)),
% 1.32/0.56    inference(backward_demodulation,[],[f72,f126])).
% 1.32/0.56  fof(f126,plain,(
% 1.32/0.56    sK0 = k2_tarski(sK1,sK1)),
% 1.32/0.56    inference(backward_demodulation,[],[f69,f121])).
% 1.32/0.56  fof(f121,plain,(
% 1.32/0.56    sK0 = k6_domain_1(sK0,sK1)),
% 1.32/0.56    inference(backward_demodulation,[],[f61,f110])).
% 1.32/0.56  fof(f110,plain,(
% 1.32/0.56    sK1 = sK2(sK0)),
% 1.32/0.56    inference(resolution,[],[f81,f57])).
% 1.32/0.56  fof(f57,plain,(
% 1.32/0.56    r2_hidden(sK1,sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f54,f28])).
% 1.32/0.56  fof(f28,plain,(
% 1.32/0.56    ~v1_xboole_0(sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f19])).
% 1.32/0.56  fof(f19,plain,(
% 1.32/0.56    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 1.32/0.56  fof(f17,plain,(
% 1.32/0.56    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f18,plain,(
% 1.32/0.56    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f11,plain,(
% 1.32/0.56    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.32/0.56    inference(flattening,[],[f10])).
% 1.32/0.56  fof(f10,plain,(
% 1.32/0.56    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f9])).
% 1.32/0.56  fof(f9,negated_conjecture,(
% 1.32/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.32/0.56    inference(negated_conjecture,[],[f8])).
% 1.32/0.56  fof(f8,conjecture,(
% 1.32/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.32/0.56  fof(f54,plain,(
% 1.32/0.56    v1_xboole_0(sK0) | r2_hidden(sK1,sK0)),
% 1.32/0.56    inference(resolution,[],[f38,f29])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    m1_subset_1(sK1,sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f19])).
% 1.32/0.56  fof(f38,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f14])).
% 1.32/0.56  fof(f14,plain,(
% 1.32/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.32/0.56    inference(flattening,[],[f13])).
% 1.32/0.56  fof(f13,plain,(
% 1.32/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.32/0.56    inference(ennf_transformation,[],[f5])).
% 1.32/0.56  fof(f5,axiom,(
% 1.32/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.32/0.56  fof(f81,plain,(
% 1.32/0.56    ( ! [X1] : (~r2_hidden(X1,sK0) | sK2(sK0) = X1) )),
% 1.32/0.56    inference(superposition,[],[f51,f79])).
% 1.32/0.56  fof(f79,plain,(
% 1.32/0.56    sK0 = k2_tarski(sK2(sK0),sK2(sK0))),
% 1.32/0.56    inference(forward_demodulation,[],[f78,f61])).
% 1.32/0.56  fof(f78,plain,(
% 1.32/0.56    k6_domain_1(sK0,sK2(sK0)) = k2_tarski(sK2(sK0),sK2(sK0))),
% 1.32/0.56    inference(subsumption_resolution,[],[f77,f28])).
% 1.32/0.56  fof(f77,plain,(
% 1.32/0.56    v1_xboole_0(sK0) | k6_domain_1(sK0,sK2(sK0)) = k2_tarski(sK2(sK0),sK2(sK0))),
% 1.32/0.56    inference(resolution,[],[f68,f31])).
% 1.32/0.56  fof(f31,plain,(
% 1.32/0.56    v1_zfmisc_1(sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f19])).
% 1.32/0.56  fof(f68,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))) )),
% 1.32/0.56    inference(duplicate_literal_removal,[],[f67])).
% 1.32/0.56  fof(f67,plain,(
% 1.32/0.56    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.32/0.56    inference(resolution,[],[f44,f35])).
% 1.32/0.56  fof(f35,plain,(
% 1.32/0.56    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f23])).
% 1.32/0.56  fof(f23,plain,(
% 1.32/0.56    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.32/0.56  fof(f22,plain,(
% 1.32/0.56    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f21,plain,(
% 1.32/0.56    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.32/0.56    inference(rectify,[],[f20])).
% 1.32/0.56  fof(f20,plain,(
% 1.32/0.56    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.32/0.56    inference(nnf_transformation,[],[f12])).
% 1.32/0.56  fof(f12,plain,(
% 1.32/0.56    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f7])).
% 1.32/0.56  fof(f7,axiom,(
% 1.32/0.56    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.32/0.56  fof(f44,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f39,f34])).
% 1.32/0.56  fof(f34,plain,(
% 1.32/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f2])).
% 1.32/0.56  fof(f2,axiom,(
% 1.32/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.56  fof(f39,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f16])).
% 1.32/0.56  fof(f16,plain,(
% 1.32/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.32/0.56    inference(flattening,[],[f15])).
% 1.32/0.56  fof(f15,plain,(
% 1.32/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f6])).
% 1.32/0.56  fof(f6,axiom,(
% 1.32/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.32/0.56  fof(f51,plain,(
% 1.32/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 1.32/0.56    inference(equality_resolution,[],[f48])).
% 1.32/0.56  fof(f48,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.32/0.56    inference(definition_unfolding,[],[f40,f34])).
% 1.32/0.56  fof(f40,plain,(
% 1.32/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.32/0.56    inference(cnf_transformation,[],[f27])).
% 1.32/0.56  fof(f27,plain,(
% 1.32/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.32/0.56  fof(f26,plain,(
% 1.32/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f25,plain,(
% 1.32/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.56    inference(rectify,[],[f24])).
% 1.32/0.56  fof(f24,plain,(
% 1.32/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.56    inference(nnf_transformation,[],[f1])).
% 1.32/0.56  % (28175)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.56  fof(f1,axiom,(
% 1.32/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.32/0.56  fof(f61,plain,(
% 1.32/0.56    sK0 = k6_domain_1(sK0,sK2(sK0))),
% 1.32/0.56    inference(subsumption_resolution,[],[f60,f28])).
% 1.32/0.56  fof(f60,plain,(
% 1.32/0.56    sK0 = k6_domain_1(sK0,sK2(sK0)) | v1_xboole_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f36,f31])).
% 1.32/0.56  fof(f36,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f23])).
% 1.32/0.56  fof(f69,plain,(
% 1.32/0.56    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 1.32/0.56    inference(subsumption_resolution,[],[f66,f28])).
% 1.32/0.56  fof(f66,plain,(
% 1.32/0.56    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(sK0)),
% 1.32/0.56    inference(resolution,[],[f44,f29])).
% 1.32/0.56  fof(f72,plain,(
% 1.32/0.56    v1_subset_1(k2_tarski(sK1,sK1),sK0)),
% 1.32/0.56    inference(backward_demodulation,[],[f30,f69])).
% 1.32/0.56  fof(f30,plain,(
% 1.32/0.56    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.32/0.56    inference(cnf_transformation,[],[f19])).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (28176)------------------------------
% 1.32/0.56  % (28176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (28176)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (28176)Memory used [KB]: 10746
% 1.32/0.56  % (28176)Time elapsed: 0.134 s
% 1.32/0.56  % (28176)------------------------------
% 1.32/0.56  % (28176)------------------------------
% 1.32/0.56  % (28169)Success in time 0.198 s
%------------------------------------------------------------------------------
