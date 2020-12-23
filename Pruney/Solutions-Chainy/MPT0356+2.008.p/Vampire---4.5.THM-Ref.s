%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:25 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 106 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  190 ( 378 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f75])).

fof(f75,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f67,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f64,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
        & r1_tarski(sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f99,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f92,f61])).

fof(f61,plain,(
    ~ r1_tarski(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f34,f58])).

fof(f58,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    ! [X0] :
      ( r1_tarski(sK2,k4_xboole_0(X0,sK1))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f89,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f89,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f38,f82])).

fof(f82,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f81,f57])).

fof(f81,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f80,plain,(
    ! [X2] :
      ( ~ r1_tarski(k4_xboole_0(X2,sK2),sK1)
      | sK1 = k4_xboole_0(X2,sK2)
      | ~ r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k4_xboole_0(X0,sK2))
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f72,f35])).

fof(f72,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f66,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f33,f63])).

fof(f63,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f47])).

fof(f33,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (8488)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.16/0.51  % (8477)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.51  % (8495)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.16/0.51  % (8487)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.16/0.52  % (8487)Refutation found. Thanks to Tanya!
% 1.16/0.52  % SZS status Theorem for theBenchmark
% 1.16/0.52  % SZS output start Proof for theBenchmark
% 1.16/0.52  fof(f103,plain,(
% 1.16/0.52    $false),
% 1.16/0.52    inference(subsumption_resolution,[],[f99,f75])).
% 1.16/0.52  fof(f75,plain,(
% 1.16/0.52    r1_tarski(sK2,sK0)),
% 1.16/0.52    inference(resolution,[],[f67,f55])).
% 1.16/0.52  fof(f55,plain,(
% 1.16/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.16/0.52    inference(equality_resolution,[],[f39])).
% 1.16/0.52  fof(f39,plain,(
% 1.16/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.16/0.52    inference(cnf_transformation,[],[f27])).
% 1.16/0.52  fof(f27,plain,(
% 1.16/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.16/0.52  fof(f26,plain,(
% 1.16/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.16/0.52    introduced(choice_axiom,[])).
% 1.16/0.52  fof(f25,plain,(
% 1.16/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/0.52    inference(rectify,[],[f24])).
% 1.16/0.52  fof(f24,plain,(
% 1.16/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/0.52    inference(nnf_transformation,[],[f7])).
% 1.16/0.52  fof(f7,axiom,(
% 1.16/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.16/0.52  fof(f67,plain,(
% 1.16/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.16/0.52    inference(subsumption_resolution,[],[f64,f52])).
% 1.16/0.52  fof(f52,plain,(
% 1.16/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.16/0.52    inference(cnf_transformation,[],[f10])).
% 1.16/0.52  fof(f10,axiom,(
% 1.16/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.16/0.52  fof(f64,plain,(
% 1.16/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.16/0.52    inference(resolution,[],[f32,f48])).
% 1.16/0.52  fof(f48,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f30])).
% 1.16/0.52  fof(f30,plain,(
% 1.16/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.16/0.52    inference(nnf_transformation,[],[f20])).
% 1.16/0.52  fof(f20,plain,(
% 1.16/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.16/0.52    inference(ennf_transformation,[],[f8])).
% 1.16/0.52  fof(f8,axiom,(
% 1.16/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.16/0.52  fof(f32,plain,(
% 1.16/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.16/0.52    inference(cnf_transformation,[],[f23])).
% 1.16/0.52  fof(f23,plain,(
% 1.16/0.52    (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22,f21])).
% 1.16/0.52  fof(f21,plain,(
% 1.16/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.16/0.52    introduced(choice_axiom,[])).
% 1.16/0.52  fof(f22,plain,(
% 1.16/0.52    ? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.16/0.52    introduced(choice_axiom,[])).
% 1.16/0.52  fof(f14,plain,(
% 1.16/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.52    inference(flattening,[],[f13])).
% 1.16/0.52  fof(f13,plain,(
% 1.16/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.52    inference(ennf_transformation,[],[f12])).
% 1.16/0.52  fof(f12,negated_conjecture,(
% 1.16/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.16/0.52    inference(negated_conjecture,[],[f11])).
% 1.16/0.52  fof(f11,conjecture,(
% 1.16/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.16/0.52  fof(f99,plain,(
% 1.16/0.52    ~r1_tarski(sK2,sK0)),
% 1.16/0.52    inference(resolution,[],[f92,f61])).
% 1.16/0.52  fof(f61,plain,(
% 1.16/0.52    ~r1_tarski(sK2,k4_xboole_0(sK0,sK1))),
% 1.16/0.52    inference(backward_demodulation,[],[f34,f58])).
% 1.16/0.52  fof(f58,plain,(
% 1.16/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.16/0.52    inference(resolution,[],[f31,f47])).
% 1.16/0.52  fof(f47,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f19])).
% 1.16/0.52  fof(f19,plain,(
% 1.16/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.52    inference(ennf_transformation,[],[f9])).
% 1.16/0.52  fof(f9,axiom,(
% 1.16/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.16/0.52  fof(f31,plain,(
% 1.16/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.52    inference(cnf_transformation,[],[f23])).
% 1.16/0.52  fof(f34,plain,(
% 1.16/0.52    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.16/0.52    inference(cnf_transformation,[],[f23])).
% 1.16/0.52  fof(f92,plain,(
% 1.16/0.52    ( ! [X0] : (r1_tarski(sK2,k4_xboole_0(X0,sK1)) | ~r1_tarski(sK2,X0)) )),
% 1.16/0.52    inference(resolution,[],[f89,f35])).
% 1.16/0.52  fof(f35,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f16])).
% 1.16/0.52  fof(f16,plain,(
% 1.16/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.16/0.52    inference(flattening,[],[f15])).
% 1.16/0.52  fof(f15,plain,(
% 1.16/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.16/0.52    inference(ennf_transformation,[],[f6])).
% 1.16/0.52  fof(f6,axiom,(
% 1.16/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.16/0.52  fof(f89,plain,(
% 1.16/0.52    r1_xboole_0(sK2,sK1)),
% 1.16/0.52    inference(resolution,[],[f86,f57])).
% 1.16/0.52  fof(f57,plain,(
% 1.16/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.16/0.52    inference(equality_resolution,[],[f43])).
% 1.16/0.52  fof(f43,plain,(
% 1.16/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.16/0.52    inference(cnf_transformation,[],[f29])).
% 1.16/0.52  fof(f29,plain,(
% 1.16/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.52    inference(flattening,[],[f28])).
% 1.16/0.52  fof(f28,plain,(
% 1.16/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.52    inference(nnf_transformation,[],[f1])).
% 1.16/0.52  fof(f1,axiom,(
% 1.16/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.16/0.52  fof(f86,plain,(
% 1.16/0.52    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK1)) )),
% 1.16/0.52    inference(superposition,[],[f38,f82])).
% 1.16/0.52  fof(f82,plain,(
% 1.16/0.52    sK1 = k4_xboole_0(sK1,sK2)),
% 1.16/0.52    inference(subsumption_resolution,[],[f81,f57])).
% 1.16/0.52  fof(f81,plain,(
% 1.16/0.52    sK1 = k4_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK1)),
% 1.16/0.52    inference(resolution,[],[f80,f46])).
% 1.16/0.52  fof(f46,plain,(
% 1.16/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f4])).
% 1.16/0.52  fof(f4,axiom,(
% 1.16/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.16/0.52  fof(f80,plain,(
% 1.16/0.52    ( ! [X2] : (~r1_tarski(k4_xboole_0(X2,sK2),sK1) | sK1 = k4_xboole_0(X2,sK2) | ~r1_tarski(sK1,X2)) )),
% 1.16/0.52    inference(resolution,[],[f74,f45])).
% 1.16/0.52  fof(f45,plain,(
% 1.16/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f29])).
% 1.16/0.52  fof(f74,plain,(
% 1.16/0.52    ( ! [X0] : (r1_tarski(sK1,k4_xboole_0(X0,sK2)) | ~r1_tarski(sK1,X0)) )),
% 1.16/0.52    inference(resolution,[],[f72,f35])).
% 1.16/0.52  fof(f72,plain,(
% 1.16/0.52    r1_xboole_0(sK1,sK2)),
% 1.16/0.52    inference(resolution,[],[f66,f37])).
% 1.16/0.52  fof(f37,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f17])).
% 1.16/0.52  fof(f17,plain,(
% 1.16/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.16/0.52    inference(ennf_transformation,[],[f3])).
% 1.16/0.52  fof(f3,axiom,(
% 1.16/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.16/0.52  fof(f66,plain,(
% 1.16/0.52    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 1.16/0.52    inference(backward_demodulation,[],[f33,f63])).
% 1.16/0.52  fof(f63,plain,(
% 1.16/0.52    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.16/0.52    inference(resolution,[],[f32,f47])).
% 1.16/0.52  fof(f33,plain,(
% 1.16/0.52    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.16/0.52    inference(cnf_transformation,[],[f23])).
% 1.16/0.52  fof(f38,plain,(
% 1.16/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.16/0.52    inference(cnf_transformation,[],[f18])).
% 1.16/0.52  fof(f18,plain,(
% 1.16/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.16/0.52    inference(ennf_transformation,[],[f5])).
% 1.16/0.52  fof(f5,axiom,(
% 1.16/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.16/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.16/0.52  % SZS output end Proof for theBenchmark
% 1.16/0.52  % (8487)------------------------------
% 1.16/0.52  % (8487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (8487)Termination reason: Refutation
% 1.16/0.52  
% 1.16/0.52  % (8487)Memory used [KB]: 1791
% 1.16/0.52  % (8487)Time elapsed: 0.069 s
% 1.16/0.52  % (8487)------------------------------
% 1.16/0.52  % (8487)------------------------------
% 1.16/0.52  % (8475)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.52  % (8485)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.16/0.52  % (8479)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.52  % (8480)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.16/0.52  % (8485)Refutation not found, incomplete strategy% (8485)------------------------------
% 1.16/0.52  % (8485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (8485)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.52  
% 1.16/0.52  % (8485)Memory used [KB]: 10618
% 1.16/0.52  % (8485)Time elapsed: 0.118 s
% 1.16/0.52  % (8485)------------------------------
% 1.16/0.52  % (8485)------------------------------
% 1.16/0.52  % (8489)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.16/0.53  % (8472)Success in time 0.165 s
%------------------------------------------------------------------------------
