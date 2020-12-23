%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:13 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  76 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 233 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(global_subsumption,[],[f19,f199])).

fof(f199,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f195,f35])).

fof(f35,plain,(
    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f34,plain,(
    r2_hidden(sK0,sK1) ),
    inference(global_subsumption,[],[f16,f33])).

fof(f33,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f195,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f73,f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(global_subsumption,[],[f20,f21,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1)
      | ~ r2_hidden(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f71,f31])).

fof(f31,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f24,f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f63,f22])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0)) ) ),
    inference(global_subsumption,[],[f16,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0)) ) ),
    inference(resolution,[],[f26,f17])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f21,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:49:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (14733)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.44  % (14749)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.44  % (14741)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.47  % (14741)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f200,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(global_subsumption,[],[f19,f199])).
% 0.19/0.47  fof(f199,plain,(
% 0.19/0.47    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.19/0.47    inference(forward_demodulation,[],[f195,f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.19/0.47    inference(resolution,[],[f34,f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    r2_hidden(sK0,sK1)),
% 0.19/0.47    inference(global_subsumption,[],[f16,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    r2_hidden(sK0,sK1) | ~v1_relat_1(sK2)),
% 0.19/0.47    inference(resolution,[],[f27,f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.47    inference(flattening,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.19/0.47    inference(negated_conjecture,[],[f7])).
% 0.19/0.47  fof(f7,conjecture,(
% 0.19/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    v1_relat_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f195,plain,(
% 0.19/0.47    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))),
% 0.19/0.47    inference(resolution,[],[f73,f34])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1)) )),
% 0.19/0.47    inference(global_subsumption,[],[f20,f21,f72])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1) | ~r2_hidden(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f71,f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.19/0.47    inference(resolution,[],[f24,f16])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1))) )),
% 0.19/0.47    inference(superposition,[],[f63,f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0))) )),
% 0.19/0.47    inference(global_subsumption,[],[f16,f47])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0))) )),
% 0.19/0.47    inference(resolution,[],[f26,f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f4])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (14741)------------------------------
% 0.19/0.47  % (14741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (14741)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (14741)Memory used [KB]: 10874
% 0.19/0.47  % (14741)Time elapsed: 0.099 s
% 0.19/0.47  % (14741)------------------------------
% 0.19/0.47  % (14741)------------------------------
% 0.19/0.47  % (14726)Success in time 0.125 s
%------------------------------------------------------------------------------
