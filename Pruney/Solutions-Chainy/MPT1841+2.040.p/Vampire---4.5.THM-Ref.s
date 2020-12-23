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
% DateTime   : Thu Dec  3 13:20:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 635 expanded)
%              Number of leaves         :   19 ( 188 expanded)
%              Depth                    :   25
%              Number of atoms          :  287 (2132 expanded)
%              Number of equality atoms :   51 ( 174 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f550,plain,(
    $false ),
    inference(subsumption_resolution,[],[f549,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f58,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f549,plain,(
    k1_xboole_0 = k1_tarski(sK2(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f535,f540])).

fof(f540,plain,(
    k1_xboole_0 = k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f260,f488])).

fof(f488,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f46,f487])).

fof(f487,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f485,f46])).

fof(f485,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f478,f357])).

fof(f357,plain,(
    ! [X0] :
      ( v1_subset_1(k1_xboole_0,X0)
      | k1_xboole_0 = sK0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f355,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f355,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | v1_subset_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f344,f52])).

% (3526)Refutation not found, incomplete strategy% (3526)------------------------------
% (3526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f344,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f341,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f68,f50])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f341,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f340,f46])).

fof(f340,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31,f30])).

fof(f30,plain,
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

% (3517)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f31,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

% (3515)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f478,plain,(
    ~ v1_subset_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f57,f443])).

fof(f443,plain,(
    k1_xboole_0 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f404,f427])).

fof(f427,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f227,f425])).

fof(f425,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f419,f73])).

fof(f419,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f397,f80])).

fof(f80,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f64,f74])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f397,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(sK1),X0)
      | sK0 = k1_tarski(sK1) ) ),
    inference(resolution,[],[f366,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

% (3526)Termination reason: Refutation not found, incomplete strategy
fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f366,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_tarski(sK1))
      | sK0 = k1_tarski(sK1) ) ),
    inference(resolution,[],[f342,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f342,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f341,f235])).

fof(f235,plain,(
    r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f233,f68])).

fof(f233,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f232,f46])).

fof(f232,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f231,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f231,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f61,f226])).

fof(f226,plain,(
    k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f217,f46])).

fof(f217,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f60,f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f227,plain,(
    v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f48,f226])).

fof(f48,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f404,plain,
    ( ~ v1_subset_1(sK0,sK0)
    | k1_xboole_0 = sK3(sK0) ),
    inference(superposition,[],[f57,f390])).

fof(f390,plain,
    ( sK0 = sK3(sK0)
    | k1_xboole_0 = sK3(sK0) ),
    inference(resolution,[],[f370,f80])).

fof(f370,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK0),X0)
      | sK0 = sK3(sK0) ) ),
    inference(resolution,[],[f364,f66])).

fof(f364,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(sK0))
      | sK0 = sK3(sK0) ) ),
    inference(resolution,[],[f350,f54])).

fof(f350,plain,
    ( v1_xboole_0(sK3(sK0))
    | sK0 = sK3(sK0) ),
    inference(resolution,[],[f341,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(sK3(X1),X1) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK3(X0),X0)
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f57,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f260,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k6_domain_1(k1_xboole_0,sK2(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f248,f114])).

fof(f114,plain,
    ( m1_subset_1(sK2(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f105,f84])).

fof(f84,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(resolution,[],[f80,f75])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK3(X0)),X0)
      | v1_xboole_0(sK3(X0)) ) ),
    inference(resolution,[],[f95,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK3(X6))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f248,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_xboole_0)
      | v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = k6_domain_1(k1_xboole_0,X4) ) ),
    inference(resolution,[],[f229,f80])).

fof(f229,plain,(
    ! [X4,X3] :
      ( r1_tarski(k6_domain_1(X4,X3),X4)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f61,f68])).

fof(f535,plain,(
    k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) = k1_tarski(sK2(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f225,f488])).

fof(f225,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) = k1_tarski(sK2(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) = k1_tarski(sK2(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f60,f114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (3511)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (3527)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (3519)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (3505)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (3509)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (3507)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  % (3504)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (3531)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (3529)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.58  % (3506)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (3530)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.58  % (3533)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (3521)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.58  % (3513)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (3520)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (3511)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (3528)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (3526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (3523)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (3525)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.59  % (3518)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f550,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f549,f73])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.22/0.59    inference(superposition,[],[f58,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.59  fof(f549,plain,(
% 0.22/0.59    k1_xboole_0 = k1_tarski(sK2(k1_xboole_0))),
% 0.22/0.59    inference(forward_demodulation,[],[f535,f540])).
% 0.22/0.59  fof(f540,plain,(
% 0.22/0.59    k1_xboole_0 = k6_domain_1(k1_xboole_0,sK2(k1_xboole_0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f260,f488])).
% 0.22/0.59  fof(f488,plain,(
% 0.22/0.59    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.59    inference(backward_demodulation,[],[f46,f487])).
% 0.22/0.59  fof(f487,plain,(
% 0.22/0.59    k1_xboole_0 = sK0),
% 0.22/0.59    inference(subsumption_resolution,[],[f485,f46])).
% 0.22/0.59  fof(f485,plain,(
% 0.22/0.59    k1_xboole_0 = sK0 | v1_xboole_0(sK0)),
% 0.22/0.59    inference(resolution,[],[f478,f357])).
% 0.22/0.59  fof(f357,plain,(
% 0.22/0.59    ( ! [X0] : (v1_subset_1(k1_xboole_0,X0) | k1_xboole_0 = sK0 | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f355,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.59  fof(f355,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = sK0 | v1_subset_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(resolution,[],[f344,f52])).
% 0.22/0.59  % (3526)Refutation not found, incomplete strategy% (3526)------------------------------
% 0.22/0.59  % (3526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.22/0.59  fof(f344,plain,(
% 0.22/0.59    v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.59    inference(resolution,[],[f341,f74])).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(resolution,[],[f68,f50])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.59    inference(nnf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.59  fof(f341,plain,(
% 0.22/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f340,f46])).
% 0.22/0.59  fof(f340,plain,(
% 0.22/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(resolution,[],[f53,f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    v1_zfmisc_1(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31,f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  % (3517)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,negated_conjecture,(
% 0.22/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.59    inference(negated_conjecture,[],[f15])).
% 0.22/0.59  fof(f15,conjecture,(
% 0.22/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f21])).
% 0.22/0.59  % (3515)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.59  fof(f478,plain,(
% 0.22/0.59    ~v1_subset_1(k1_xboole_0,sK0)),
% 0.22/0.59    inference(superposition,[],[f57,f443])).
% 0.22/0.59  fof(f443,plain,(
% 0.22/0.59    k1_xboole_0 = sK3(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f404,f427])).
% 0.22/0.59  fof(f427,plain,(
% 0.22/0.59    v1_subset_1(sK0,sK0)),
% 0.22/0.59    inference(backward_demodulation,[],[f227,f425])).
% 0.22/0.59  fof(f425,plain,(
% 0.22/0.59    sK0 = k1_tarski(sK1)),
% 0.22/0.59    inference(subsumption_resolution,[],[f419,f73])).
% 0.22/0.59  fof(f419,plain,(
% 0.22/0.59    sK0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.59    inference(resolution,[],[f397,f80])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.22/0.59    inference(resolution,[],[f64,f74])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(flattening,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f397,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_tarski(sK1),X0) | sK0 = k1_tarski(sK1)) )),
% 0.22/0.59    inference(resolution,[],[f366,f66])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(rectify,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(nnf_transformation,[],[f27])).
% 0.22/0.59  % (3526)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.59  fof(f366,plain,(
% 0.22/0.59    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK1)) | sK0 = k1_tarski(sK1)) )),
% 0.22/0.59    inference(resolution,[],[f342,f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.59    inference(rectify,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.59    inference(nnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.59  fof(f342,plain,(
% 0.22/0.59    v1_xboole_0(k1_tarski(sK1)) | sK0 = k1_tarski(sK1)),
% 0.22/0.59    inference(resolution,[],[f341,f235])).
% 0.22/0.59  fof(f235,plain,(
% 0.22/0.59    r1_tarski(k1_tarski(sK1),sK0)),
% 0.22/0.59    inference(resolution,[],[f233,f68])).
% 0.22/0.59  fof(f233,plain,(
% 0.22/0.59    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f232,f46])).
% 0.22/0.59  fof(f232,plain,(
% 0.22/0.59    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f231,f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    m1_subset_1(sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f231,plain,(
% 0.22/0.59    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.22/0.59    inference(superposition,[],[f61,f226])).
% 0.22/0.59  fof(f226,plain,(
% 0.22/0.59    k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.22/0.59    inference(subsumption_resolution,[],[f217,f46])).
% 0.22/0.59  fof(f217,plain,(
% 0.22/0.59    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0)),
% 0.22/0.59    inference(resolution,[],[f60,f47])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.59    inference(flattening,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.59  fof(f227,plain,(
% 0.22/0.59    v1_subset_1(k1_tarski(sK1),sK0)),
% 0.22/0.59    inference(backward_demodulation,[],[f48,f226])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f404,plain,(
% 0.22/0.59    ~v1_subset_1(sK0,sK0) | k1_xboole_0 = sK3(sK0)),
% 0.22/0.59    inference(superposition,[],[f57,f390])).
% 0.22/0.59  fof(f390,plain,(
% 0.22/0.59    sK0 = sK3(sK0) | k1_xboole_0 = sK3(sK0)),
% 0.22/0.59    inference(resolution,[],[f370,f80])).
% 0.22/0.59  fof(f370,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(sK3(sK0),X0) | sK0 = sK3(sK0)) )),
% 0.22/0.59    inference(resolution,[],[f364,f66])).
% 0.22/0.59  fof(f364,plain,(
% 0.22/0.59    ( ! [X1] : (~r2_hidden(X1,sK3(sK0)) | sK0 = sK3(sK0)) )),
% 0.22/0.59    inference(resolution,[],[f350,f54])).
% 0.22/0.59  fof(f350,plain,(
% 0.22/0.59    v1_xboole_0(sK3(sK0)) | sK0 = sK3(sK0)),
% 0.22/0.59    inference(resolution,[],[f341,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X1] : (r1_tarski(sK3(X1),X1)) )),
% 0.22/0.59    inference(resolution,[],[f68,f56])).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0] : (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ~v1_xboole_0(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f260,plain,(
% 0.22/0.59    v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k6_domain_1(k1_xboole_0,sK2(k1_xboole_0))),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f253])).
% 0.22/0.59  fof(f253,plain,(
% 0.22/0.59    v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) | v1_xboole_0(k1_xboole_0)),
% 0.22/0.59    inference(resolution,[],[f248,f114])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    m1_subset_1(sK2(k1_xboole_0),k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f105,f84])).
% 0.22/0.59  fof(f84,plain,(
% 0.22/0.59    k1_xboole_0 = sK3(k1_xboole_0)),
% 0.22/0.59    inference(resolution,[],[f80,f75])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(sK2(sK3(X0)),X0) | v1_xboole_0(sK3(X0))) )),
% 0.22/0.59    inference(resolution,[],[f95,f55])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f95,plain,(
% 0.22/0.59    ( ! [X6,X5] : (~r2_hidden(X5,sK3(X6)) | m1_subset_1(X5,X6)) )),
% 0.22/0.59    inference(resolution,[],[f70,f56])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.59    inference(flattening,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.59  fof(f248,plain,(
% 0.22/0.59    ( ! [X4] : (~m1_subset_1(X4,k1_xboole_0) | v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k6_domain_1(k1_xboole_0,X4)) )),
% 0.22/0.59    inference(resolution,[],[f229,f80])).
% 0.22/0.59  fof(f229,plain,(
% 0.22/0.59    ( ! [X4,X3] : (r1_tarski(k6_domain_1(X4,X3),X4) | v1_xboole_0(X4) | ~m1_subset_1(X3,X4)) )),
% 0.22/0.59    inference(resolution,[],[f61,f68])).
% 0.22/0.59  fof(f535,plain,(
% 0.22/0.59    k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) = k1_tarski(sK2(k1_xboole_0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f225,f488])).
% 0.22/0.59  fof(f225,plain,(
% 0.22/0.59    v1_xboole_0(k1_xboole_0) | k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) = k1_tarski(sK2(k1_xboole_0))),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f220])).
% 0.22/0.59  fof(f220,plain,(
% 0.22/0.59    k6_domain_1(k1_xboole_0,sK2(k1_xboole_0)) = k1_tarski(sK2(k1_xboole_0)) | v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 0.22/0.59    inference(resolution,[],[f60,f114])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (3511)------------------------------
% 0.22/0.59  % (3511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3511)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (3511)Memory used [KB]: 6524
% 0.22/0.59  % (3511)Time elapsed: 0.160 s
% 0.22/0.59  % (3511)------------------------------
% 0.22/0.59  % (3511)------------------------------
% 0.22/0.59  
% 0.22/0.59  % (3526)Memory used [KB]: 10746
% 0.22/0.59  % (3526)Time elapsed: 0.087 s
% 0.22/0.59  % (3526)------------------------------
% 0.22/0.59  % (3526)------------------------------
% 0.22/0.59  % (3514)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (3503)Success in time 0.229 s
%------------------------------------------------------------------------------
