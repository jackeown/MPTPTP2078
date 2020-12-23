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
% DateTime   : Thu Dec  3 12:53:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  87 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  156 ( 301 expanded)
%              Number of equality atoms :   23 (  59 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f88])).

fof(f88,plain,(
    ! [X1] : v1_relat_1(k8_relat_1(X1,sK2)) ),
    inference(subsumption_resolution,[],[f87,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f87,plain,(
    ! [X1] :
      ( v1_relat_1(k8_relat_1(X1,sK2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f84,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

fof(f84,plain,(
    ! [X1] :
      ( v1_relat_1(k8_relat_1(X1,sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(resolution,[],[f18,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f140,plain,(
    ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f83,f92])).

fof(f92,plain,(
    ! [X3] : v1_funct_1(k8_relat_1(X3,sK2)) ),
    inference(subsumption_resolution,[],[f91,f23])).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X3] :
      ( v1_funct_1(k8_relat_1(X3,sK2))
      | ~ v1_funct_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f90,f22])).

fof(f90,plain,(
    ! [X3] :
      ( v1_funct_1(k8_relat_1(X3,sK2))
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_funct_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f89,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f89,plain,(
    ! [X3] :
      ( v1_funct_1(k8_relat_1(X3,sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_funct_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f86,f18])).

fof(f86,plain,(
    ! [X3] :
      ( v1_funct_1(k8_relat_1(X3,sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_funct_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f26,f41])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f83,plain,
    ( ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f82,f21])).

fof(f21,plain,(
    k1_funct_1(k8_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f81,f19])).

fof(f81,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ v1_funct_1(sK2)
    | k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f74,f18])).

fof(f74,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,sK0) ),
    inference(resolution,[],[f20,f40])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k8_relat_1(X0,X2))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X0,X2)))
      | k1_funct_1(X2,X3) = k1_funct_1(k8_relat_1(X0,X2),X3) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(f20,plain,(
    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (9857)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.46  % (9849)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.46  % (9851)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (9852)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (9851)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (9842)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK2))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f84,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.47    inference(superposition,[],[f37,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f18,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.21/0.47    inference(resolution,[],[f83,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X3] : (v1_funct_1(k8_relat_1(X3,sK2))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f91,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X3] : (v1_funct_1(k8_relat_1(X3,sK2)) | ~v1_funct_1(k6_relat_1(X3))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f22])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X3] : (v1_funct_1(k8_relat_1(X3,sK2)) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_funct_1(k6_relat_1(X3))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X3] : (v1_funct_1(k8_relat_1(X3,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_funct_1(k6_relat_1(X3))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f18])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X3] : (v1_funct_1(k8_relat_1(X3,sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_funct_1(k6_relat_1(X3))) )),
% 0.21/0.47    inference(superposition,[],[f26,f41])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k1_funct_1(k8_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f19])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~v1_funct_1(sK2) | k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f18])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,sK0)),
% 0.21/0.47    inference(resolution,[],[f20,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (~v1_relat_1(k8_relat_1(X0,X2)) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X3,k1_relat_1(k8_relat_1(X0,X2))) | k1_funct_1(X2,X3) = k1_funct_1(k8_relat_1(X0,X2),X3)) )),
% 0.21/0.47    inference(equality_resolution,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X3,k1_relat_1(X1)) | k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | k8_relat_1(X0,X2) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.21/0.47    inference(rectify,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9851)------------------------------
% 0.21/0.47  % (9851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9851)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9851)Memory used [KB]: 1663
% 0.21/0.47  % (9851)Time elapsed: 0.066 s
% 0.21/0.47  % (9851)------------------------------
% 0.21/0.47  % (9851)------------------------------
% 0.21/0.47  % (9844)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (9837)Success in time 0.115 s
%------------------------------------------------------------------------------
