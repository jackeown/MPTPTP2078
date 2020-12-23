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
% DateTime   : Thu Dec  3 13:06:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 806 expanded)
%              Number of leaves         :    5 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 (4302 expanded)
%              Number of equality atoms :   52 (2013 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(subsumption_resolution,[],[f62,f54])).

fof(f54,plain,(
    ~ v1_partfun1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f47])).

fof(f47,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f42,f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f42,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f41,f33])).

fof(f41,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f40,f31])).

fof(f31,plain,(
    sK2 = k3_partfun1(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f17,f19,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f18,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | k1_xboole_0 = X4
      | ~ v1_funct_2(sK2,X5,X4)
      | v1_partfun1(k3_partfun1(sK2,X5,X4),X5) ) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).

fof(f33,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f17,f19,f32,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k5_partfun1(X0,X1,X2) != k1_tarski(X2) )
        & ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f32,plain,(
    k1_tarski(sK2) != k5_partfun1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f21,f31])).

fof(f21,plain,(
    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    v1_partfun1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f56,f52])).

fof(f52,plain,(
    sK2 = k3_partfun1(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f44,f47])).

fof(f44,plain,(
    sK2 = k3_partfun1(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f42])).

fof(f56,plain,(
    v1_partfun1(k3_partfun1(sK2,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f17,f51,f50,f27])).

fof(f27,plain,(
    ! [X2,X1] :
      ( v1_partfun1(k3_partfun1(X2,k1_xboole_0,X1),k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f19,f42])).

fof(f51,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f47])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f18,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:44:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (20129)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (20137)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (20138)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (20130)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (20139)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (20139)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f62,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~v1_partfun1(sK2,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f33,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    k1_xboole_0 = sK0),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f42,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    k1_xboole_0 = sK1),
% 0.22/0.51    inference(subsumption_resolution,[],[f41,f33])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    v1_partfun1(sK2,sK0) | k1_xboole_0 = sK1),
% 0.22/0.51    inference(forward_demodulation,[],[f40,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    sK2 = k3_partfun1(sK2,sK0,sK1)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f17,f19,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f39,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.22/0.51    inference(resolution,[],[f30,f19])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k1_xboole_0 = X4 | ~v1_funct_2(sK2,X5,X4) | v1_partfun1(k3_partfun1(sK2,X5,X4),X5)) )),
% 0.22/0.51    inference(resolution,[],[f17,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(k3_partfun1(X2,X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_partfun1(k3_partfun1(X2,X0,X1),X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v1_partfun1(k3_partfun1(X2,X0,X1),X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ~v1_partfun1(sK2,sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f17,f19,f32,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = k1_tarski(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | k5_partfun1(X0,X1,X2) != k1_tarski(X2)) & (k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    k1_tarski(sK2) != k5_partfun1(sK0,sK1,sK2)),
% 0.22/0.51    inference(backward_demodulation,[],[f21,f31])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    v1_partfun1(sK2,k1_xboole_0)),
% 0.22/0.51    inference(forward_demodulation,[],[f56,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    sK2 = k3_partfun1(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f44,f47])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    sK2 = k3_partfun1(sK2,sK0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f31,f42])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    v1_partfun1(k3_partfun1(sK2,k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f17,f51,f50,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_partfun1(k3_partfun1(X2,k1_xboole_0,X1),k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_partfun1(k3_partfun1(X2,X0,X1),X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f46,f47])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f19,f42])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f45,f47])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f18,f42])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (20139)------------------------------
% 0.22/0.51  % (20139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20139)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (20139)Memory used [KB]: 6140
% 0.22/0.51  % (20139)Time elapsed: 0.074 s
% 0.22/0.51  % (20139)------------------------------
% 0.22/0.51  % (20139)------------------------------
% 0.22/0.51  % (20123)Success in time 0.137 s
%------------------------------------------------------------------------------
