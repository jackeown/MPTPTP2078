%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:18 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 107 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 ( 411 expanded)
%              Number of equality atoms :   37 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f35])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).

fof(f27,plain,
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

fof(f28,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f136,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f100])).

fof(f100,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f96,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,X3)
      | ~ v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f91,f78])).

fof(f78,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,X3)
      | ~ r2_hidden(X4,X2)
      | ~ v1_xboole_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X3)
      | ~ v1_xboole_0(X3) ) ),
    inference(superposition,[],[f53,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f39,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X3)
      | ~ v1_xboole_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X3)
      | ~ v1_xboole_0(X3) ) ),
    inference(superposition,[],[f55,f61])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f134,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f133,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

% (11214)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f133,plain,(
    v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f132,f35])).

fof(f132,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f36])).

fof(f131,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f38,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ v1_zfmisc_1(sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f98,f37])).

fof(f37,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | v1_xboole_0(k6_domain_1(X0,X1))
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (11211)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.52  % (11207)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.53  % (11215)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.24/0.53  % (11212)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.53  % (11207)Refutation not found, incomplete strategy% (11207)------------------------------
% 1.24/0.53  % (11207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (11207)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (11207)Memory used [KB]: 1663
% 1.24/0.53  % (11207)Time elapsed: 0.104 s
% 1.24/0.53  % (11207)------------------------------
% 1.24/0.53  % (11207)------------------------------
% 1.24/0.53  % (11215)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f137,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(subsumption_resolution,[],[f136,f35])).
% 1.24/0.53  fof(f35,plain,(
% 1.24/0.53    ~v1_xboole_0(sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.24/0.53    inference(flattening,[],[f14])).
% 1.24/0.53  fof(f14,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f13])).
% 1.24/0.53  fof(f13,negated_conjecture,(
% 1.24/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.24/0.53    inference(negated_conjecture,[],[f12])).
% 1.24/0.53  fof(f12,conjecture,(
% 1.24/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.24/0.53  fof(f136,plain,(
% 1.24/0.53    v1_xboole_0(sK0)),
% 1.24/0.53    inference(subsumption_resolution,[],[f135,f36])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    m1_subset_1(sK1,sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f29])).
% 1.24/0.53  fof(f135,plain,(
% 1.24/0.53    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 1.24/0.53    inference(subsumption_resolution,[],[f134,f100])).
% 1.24/0.53  fof(f100,plain,(
% 1.24/0.53    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.24/0.53    inference(resolution,[],[f96,f57])).
% 1.24/0.53  fof(f57,plain,(
% 1.24/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.24/0.53    inference(equality_resolution,[],[f56])).
% 1.24/0.53  fof(f56,plain,(
% 1.24/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.24/0.53    inference(equality_resolution,[],[f49])).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.24/0.53    inference(cnf_transformation,[],[f33])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.53    inference(rectify,[],[f30])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.53    inference(nnf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.24/0.53  fof(f96,plain,(
% 1.24/0.53    ( ! [X4,X3] : (~r2_hidden(X4,X3) | ~v1_xboole_0(X3)) )),
% 1.24/0.53    inference(subsumption_resolution,[],[f91,f78])).
% 1.24/0.54  fof(f78,plain,(
% 1.24/0.54    ( ! [X4,X2,X3] : (~r2_hidden(X4,X3) | ~r2_hidden(X4,X2) | ~v1_xboole_0(X3)) )),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f77])).
% 1.24/0.54  fof(f77,plain,(
% 1.24/0.54    ( ! [X4,X2,X3] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X3) | ~v1_xboole_0(X3)) )),
% 1.24/0.54    inference(superposition,[],[f53,f61])).
% 1.24/0.54  fof(f61,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 1.24/0.54    inference(superposition,[],[f39,f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f16])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.24/0.54  fof(f53,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f34])).
% 1.24/0.54  fof(f34,plain,(
% 1.24/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.24/0.54    inference(nnf_transformation,[],[f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.24/0.54    inference(ennf_transformation,[],[f2])).
% 1.24/0.54  fof(f2,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.24/0.54  fof(f91,plain,(
% 1.24/0.54    ( ! [X4,X2,X3] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X3) | ~v1_xboole_0(X3)) )),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f90])).
% 1.24/0.54  fof(f90,plain,(
% 1.24/0.54    ( ! [X4,X2,X3] : (r2_hidden(X4,X2) | r2_hidden(X4,X2) | ~r2_hidden(X4,X3) | ~v1_xboole_0(X3)) )),
% 1.24/0.54    inference(superposition,[],[f55,f61])).
% 1.24/0.54  fof(f55,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f34])).
% 1.24/0.54  fof(f134,plain,(
% 1.24/0.54    v1_xboole_0(k1_tarski(sK1)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 1.24/0.54    inference(superposition,[],[f133,f46])).
% 1.24/0.54  fof(f46,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.24/0.54    inference(flattening,[],[f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f10])).
% 1.24/0.54  fof(f10,axiom,(
% 1.24/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.24/0.54  % (11214)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.24/0.54  fof(f133,plain,(
% 1.24/0.54    v1_xboole_0(k6_domain_1(sK0,sK1))),
% 1.24/0.54    inference(subsumption_resolution,[],[f132,f35])).
% 1.24/0.54  fof(f132,plain,(
% 1.24/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 1.24/0.54    inference(subsumption_resolution,[],[f131,f36])).
% 1.24/0.54  fof(f131,plain,(
% 1.24/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 1.24/0.54    inference(subsumption_resolution,[],[f128,f38])).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    v1_zfmisc_1(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f29])).
% 1.24/0.54  fof(f128,plain,(
% 1.24/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~v1_zfmisc_1(sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 1.24/0.54    inference(resolution,[],[f98,f37])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f29])).
% 1.24/0.54  fof(f98,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) | v1_xboole_0(k6_domain_1(X0,X1)) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.54    inference(resolution,[],[f59,f47])).
% 1.24/0.54  fof(f47,plain,(
% 1.24/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.24/0.54    inference(flattening,[],[f24])).
% 1.24/0.54  fof(f24,plain,(
% 1.24/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.24/0.54  fof(f59,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f43,f42])).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f17])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 1.24/0.54  fof(f43,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.24/0.54    inference(flattening,[],[f18])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f11])).
% 1.24/0.54  fof(f11,axiom,(
% 1.24/0.54    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (11215)------------------------------
% 1.24/0.54  % (11215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (11215)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (11215)Memory used [KB]: 1791
% 1.24/0.54  % (11215)Time elapsed: 0.103 s
% 1.24/0.54  % (11215)------------------------------
% 1.24/0.54  % (11215)------------------------------
% 1.24/0.54  % (11205)Success in time 0.169 s
%------------------------------------------------------------------------------
