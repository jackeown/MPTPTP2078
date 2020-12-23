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
% DateTime   : Thu Dec  3 12:46:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 114 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 536 expanded)
%              Number of equality atoms :   20 (  63 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f56,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f52,f43])).

fof(f43,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1),sK2)
      | r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ r2_hidden(sK3(sK1,X1),sK1)
      | r2_hidden(sK3(sK1,X1),sK2) ) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK1,X0),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f52,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f51,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    sK2 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f50,f26])).

fof(f50,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f44,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | ~ r2_hidden(sK3(sK2,X0),sK2)
      | r2_hidden(sK3(sK2,X0),sK1) ) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0))
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (5096)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (5104)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (5087)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (5085)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (5088)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (5089)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (5089)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f56,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    sK1 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(nnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    sK1 = sK2),
% 0.22/0.52    inference(forward_demodulation,[],[f52,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    sK1 = k3_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(resolution,[],[f42,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(resolution,[],[f39,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.52    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK3(sK1,X1),sK2) | r1_tarski(sK1,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f37,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK3(sK1,X1),sK1) | r2_hidden(sK3(sK1,X1),sK2)) )),
% 0.22/0.52    inference(resolution,[],[f34,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK3(sK1,X0),k1_zfmisc_1(sK0)) | r1_tarski(sK1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f33,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK3(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 0.22/0.52    inference(resolution,[],[f29,f27])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    sK2 = k3_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(superposition,[],[f51,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    sK2 = k3_xboole_0(sK2,sK1)),
% 0.22/0.52    inference(resolution,[],[f50,f26])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    r1_tarski(sK2,sK1)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.22/0.52    inference(resolution,[],[f47,f28])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f44,f27])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(sK2,X0) | ~r2_hidden(sK3(sK2,X0),sK2) | r2_hidden(sK3(sK2,X0),sK1)) )),
% 0.22/0.52    inference(resolution,[],[f35,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X1] : (m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0)) | r1_tarski(sK2,X1)) )),
% 0.22/0.52    inference(resolution,[],[f33,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (5089)------------------------------
% 0.22/0.52  % (5089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5089)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (5089)Memory used [KB]: 6268
% 0.22/0.52  % (5089)Time elapsed: 0.102 s
% 0.22/0.52  % (5089)------------------------------
% 0.22/0.52  % (5089)------------------------------
% 0.22/0.52  % (5081)Success in time 0.161 s
%------------------------------------------------------------------------------
