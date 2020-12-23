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
% DateTime   : Thu Dec  3 12:53:01 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 164 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   19
%              Number of atoms          :  198 ( 572 expanded)
%              Number of equality atoms :   35 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f25])).

fof(f25,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f76,plain,(
    ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f75,f62])).

fof(f62,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f61,plain,
    ( ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f59,f22])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f75,plain,(
    ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f74,f21])).

fof(f74,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f71,f22])).

fof(f71,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(sK0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f24,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f65,f43])).

fof(f43,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f41,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f39,f22])).

fof(f39,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f27,f38])).

fof(f38,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f37,f21])).

fof(f37,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f35,f22])).

fof(f35,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f63,f46])).

fof(f46,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f44,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f40,f22])).

fof(f40,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f26,f38])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f33,f54])).

fof(f54,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f21])).

fof(f53,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f51,f22])).

fof(f51,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f30,f23])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1251246080)
% 0.14/0.38  ipcrm: permission denied for id (1251278854)
% 0.14/0.40  ipcrm: permission denied for id (1251311635)
% 0.14/0.41  ipcrm: permission denied for id (1251344412)
% 0.22/0.44  ipcrm: permission denied for id (1251442743)
% 0.87/0.65  % (8608)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.87/0.65  % (8616)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.87/0.65  % (8608)Refutation found. Thanks to Tanya!
% 0.87/0.65  % SZS status Theorem for theBenchmark
% 0.87/0.65  % SZS output start Proof for theBenchmark
% 0.87/0.65  fof(f77,plain,(
% 0.87/0.65    $false),
% 0.87/0.65    inference(subsumption_resolution,[],[f76,f25])).
% 0.87/0.65  fof(f25,plain,(
% 0.87/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.87/0.65    inference(cnf_transformation,[],[f4])).
% 0.87/0.65  fof(f4,axiom,(
% 0.87/0.65    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.87/0.65  fof(f76,plain,(
% 0.87/0.65    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.87/0.65    inference(forward_demodulation,[],[f75,f62])).
% 0.87/0.65  fof(f62,plain,(
% 0.87/0.65    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f61,f21])).
% 0.87/0.65  fof(f21,plain,(
% 0.87/0.65    v1_relat_1(sK0)),
% 0.87/0.65    inference(cnf_transformation,[],[f10])).
% 0.87/0.65  fof(f10,plain,(
% 0.87/0.65    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.87/0.65    inference(flattening,[],[f9])).
% 0.87/0.65  fof(f9,plain,(
% 0.87/0.65    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.87/0.65    inference(ennf_transformation,[],[f8])).
% 0.87/0.65  fof(f8,negated_conjecture,(
% 0.87/0.65    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.87/0.65    inference(negated_conjecture,[],[f7])).
% 0.87/0.65  fof(f7,conjecture,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.87/0.65  fof(f61,plain,(
% 0.87/0.65    ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f59,f22])).
% 0.87/0.65  fof(f22,plain,(
% 0.87/0.65    v1_funct_1(sK0)),
% 0.87/0.65    inference(cnf_transformation,[],[f10])).
% 0.87/0.65  fof(f59,plain,(
% 0.87/0.65    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.87/0.65    inference(resolution,[],[f32,f23])).
% 0.87/0.65  fof(f23,plain,(
% 0.87/0.65    v2_funct_1(sK0)),
% 0.87/0.65    inference(cnf_transformation,[],[f10])).
% 0.87/0.65  fof(f32,plain,(
% 0.87/0.65    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.87/0.65    inference(cnf_transformation,[],[f18])).
% 0.87/0.65  fof(f18,plain,(
% 0.87/0.65    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.87/0.65    inference(flattening,[],[f17])).
% 0.87/0.65  fof(f17,plain,(
% 0.87/0.65    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.87/0.65    inference(ennf_transformation,[],[f6])).
% 0.87/0.65  fof(f6,axiom,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.87/0.65  fof(f75,plain,(
% 0.87/0.65    ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f74,f21])).
% 0.87/0.65  fof(f74,plain,(
% 0.87/0.65    ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f71,f22])).
% 0.87/0.65  fof(f71,plain,(
% 0.87/0.65    ~v1_funct_1(sK0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(equality_resolution,[],[f67])).
% 0.87/0.65  fof(f67,plain,(
% 0.87/0.65    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0)) )),
% 0.87/0.65    inference(subsumption_resolution,[],[f66,f24])).
% 0.87/0.65  fof(f24,plain,(
% 0.87/0.65    ~v2_funct_1(k2_funct_1(sK0))),
% 0.87/0.65    inference(cnf_transformation,[],[f10])).
% 0.87/0.65  fof(f66,plain,(
% 0.87/0.65    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK0))) )),
% 0.87/0.65    inference(subsumption_resolution,[],[f65,f43])).
% 0.87/0.65  fof(f43,plain,(
% 0.87/0.65    v1_funct_1(k2_funct_1(sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f42,f21])).
% 0.87/0.65  fof(f42,plain,(
% 0.87/0.65    v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f41,f23])).
% 0.87/0.65  fof(f41,plain,(
% 0.87/0.65    v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f39,f22])).
% 0.87/0.65  fof(f39,plain,(
% 0.87/0.65    v1_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(superposition,[],[f27,f38])).
% 0.87/0.65  fof(f38,plain,(
% 0.87/0.65    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f37,f21])).
% 0.87/0.65  fof(f37,plain,(
% 0.87/0.65    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f35,f22])).
% 0.87/0.65  fof(f35,plain,(
% 0.87/0.65    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.87/0.65    inference(resolution,[],[f28,f23])).
% 0.87/0.65  fof(f28,plain,(
% 0.87/0.65    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = k4_relat_1(X0)) )),
% 0.87/0.65    inference(cnf_transformation,[],[f14])).
% 0.87/0.65  fof(f14,plain,(
% 0.87/0.65    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.87/0.65    inference(flattening,[],[f13])).
% 0.87/0.65  fof(f13,plain,(
% 0.87/0.65    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.87/0.65    inference(ennf_transformation,[],[f1])).
% 0.87/0.65  fof(f1,axiom,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.87/0.65  fof(f27,plain,(
% 0.87/0.65    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.87/0.65    inference(cnf_transformation,[],[f12])).
% 0.87/0.65  fof(f12,plain,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.87/0.65    inference(flattening,[],[f11])).
% 0.87/0.65  fof(f11,plain,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.87/0.65    inference(ennf_transformation,[],[f2])).
% 0.87/0.65  fof(f2,axiom,(
% 0.87/0.65    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.87/0.65  fof(f65,plain,(
% 0.87/0.65    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK0))) )),
% 0.87/0.65    inference(subsumption_resolution,[],[f63,f46])).
% 0.87/0.65  fof(f46,plain,(
% 0.87/0.65    v1_relat_1(k2_funct_1(sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f45,f21])).
% 0.87/0.65  fof(f45,plain,(
% 0.87/0.65    v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f44,f23])).
% 0.87/0.65  fof(f44,plain,(
% 0.87/0.65    v1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(subsumption_resolution,[],[f40,f22])).
% 0.87/0.65  fof(f40,plain,(
% 0.87/0.65    v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.87/0.65    inference(superposition,[],[f26,f38])).
% 0.87/0.65  fof(f26,plain,(
% 0.87/0.65    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.87/0.65    inference(cnf_transformation,[],[f12])).
% 0.87/0.65  fof(f63,plain,(
% 0.87/0.65    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK0))) )),
% 0.87/0.65    inference(superposition,[],[f33,f54])).
% 0.87/0.65  fof(f54,plain,(
% 0.87/0.65    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f53,f21])).
% 0.87/0.65  fof(f53,plain,(
% 0.87/0.65    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.87/0.65    inference(subsumption_resolution,[],[f51,f22])).
% 0.87/0.65  fof(f51,plain,(
% 0.87/0.65    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.87/0.65    inference(resolution,[],[f30,f23])).
% 0.87/0.65  fof(f30,plain,(
% 0.87/0.65    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.87/0.65    inference(cnf_transformation,[],[f16])).
% 0.87/0.65  fof(f16,plain,(
% 0.87/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.87/0.65    inference(flattening,[],[f15])).
% 0.87/0.65  fof(f15,plain,(
% 0.87/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.87/0.65    inference(ennf_transformation,[],[f5])).
% 0.87/0.65  fof(f5,axiom,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.87/0.65  fof(f33,plain,(
% 0.87/0.65    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.87/0.65    inference(cnf_transformation,[],[f20])).
% 0.87/0.65  fof(f20,plain,(
% 0.87/0.65    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.87/0.65    inference(flattening,[],[f19])).
% 0.87/0.65  fof(f19,plain,(
% 0.87/0.65    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.87/0.65    inference(ennf_transformation,[],[f3])).
% 0.87/0.65  fof(f3,axiom,(
% 0.87/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.87/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.87/0.65  % SZS output end Proof for theBenchmark
% 0.87/0.65  % (8608)------------------------------
% 0.87/0.65  % (8608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.87/0.65  % (8608)Termination reason: Refutation
% 0.87/0.65  
% 0.87/0.65  % (8608)Memory used [KB]: 6140
% 0.87/0.65  % (8608)Time elapsed: 0.062 s
% 0.87/0.65  % (8608)------------------------------
% 0.87/0.65  % (8608)------------------------------
% 0.87/0.66  % (8458)Success in time 0.29 s
%------------------------------------------------------------------------------
