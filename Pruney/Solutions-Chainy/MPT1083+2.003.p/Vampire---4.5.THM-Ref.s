%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 115 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   20
%              Number of atoms          :  195 ( 559 expanded)
%              Number of equality atoms :   38 (  82 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12486)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f26])).

fof(f26,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

fof(f88,plain,(
    ~ v5_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f85,f47])).

fof(f47,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f52,f30])).

fof(f30,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f51,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK1,X0)
      | ~ v4_relat_1(sK1,X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f83,f49])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

% (12492)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f83,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | ~ v4_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_partfun1(sK1,X0) ) ),
    inference(superposition,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f81,plain,(
    ~ v5_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(sK1) != X0
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f78,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(sK1) != X0
      | ~ v1_relat_1(sK2)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | k1_relat_1(sK1) != X0 ) ),
    inference(forward_demodulation,[],[f75,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f74,f25])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k1_relat_1(sK2)
      | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f58,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0))
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f57,f25])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0))
      | ~ v1_relat_1(sK2)
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f54,f49])).

fof(f54,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f28,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f28,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.48  % (12477)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (12477)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  % (12486)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f88,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v5_relat_1(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ~v5_relat_1(sK2,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f85,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v4_relat_1(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f31,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ~v4_relat_1(sK1,sK0) | ~v5_relat_1(sK2,sK0)),
% 0.22/0.48    inference(resolution,[],[f84,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    v1_partfun1(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f52,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f51,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    v1_xboole_0(sK0) | ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f31,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_partfun1(sK1,X0) | ~v4_relat_1(sK1,X0) | ~v5_relat_1(sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f83,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f31,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.48  % (12492)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (~v5_relat_1(sK2,X0) | ~v4_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v1_partfun1(sK1,X0)) )),
% 0.22/0.48    inference(superposition,[],[f81,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_partfun1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~v5_relat_1(sK2,k1_relat_1(sK1))),
% 0.22/0.48    inference(equality_resolution,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK1) != X0 | ~v5_relat_1(sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f78,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK1) != X0 | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,X0)) )),
% 0.22/0.48    inference(resolution,[],[f76,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | k1_relat_1(sK1) != X0) )),
% 0.22/0.48    inference(forward_demodulation,[],[f75,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f25])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f73,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK2) != k1_relat_1(sK2) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.22/0.48    inference(superposition,[],[f58,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0)) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f57,f25])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f54,f49])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(superposition,[],[f28,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (12477)------------------------------
% 0.22/0.48  % (12477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12477)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (12477)Memory used [KB]: 10618
% 0.22/0.48  % (12477)Time elapsed: 0.056 s
% 0.22/0.48  % (12477)------------------------------
% 0.22/0.48  % (12477)------------------------------
% 0.22/0.49  % (12475)Success in time 0.117 s
%------------------------------------------------------------------------------
