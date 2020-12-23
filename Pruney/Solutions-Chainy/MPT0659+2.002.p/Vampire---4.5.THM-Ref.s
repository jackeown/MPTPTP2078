%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 123 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 ( 633 expanded)
%              Number of equality atoms :   32 (  96 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f128,f43])).

fof(f43,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f36,f41])).

fof(f41,plain,(
    k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f23,f16])).

% (30836)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f36,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f33,f35])).

fof(f35,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f34,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f17,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f33,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f20,f32])).

fof(f32,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f31,f21])).

fof(f31,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f29,f22])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f128,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f127,f21])).

fof(f127,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f119,f22])).

fof(f119,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f100,f18])).

fof(f100,plain,(
    ! [X6] :
      ( ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k4_relat_1(k5_relat_1(X6,sK1)) = k2_funct_1(k5_relat_1(X6,sK1)) ) ),
    inference(subsumption_resolution,[],[f99,f17])).

fof(f99,plain,(
    ! [X6] :
      ( ~ v2_funct_1(X6)
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k4_relat_1(k5_relat_1(X6,sK1)) = k2_funct_1(k5_relat_1(X6,sK1)) ) ),
    inference(subsumption_resolution,[],[f90,f16])).

fof(f90,plain,(
    ! [X6] :
      ( ~ v2_funct_1(X6)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k4_relat_1(k5_relat_1(X6,sK1)) = k2_funct_1(k5_relat_1(X6,sK1)) ) ),
    inference(resolution,[],[f73,f19])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f65,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (30839)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (30845)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.47  % (30845)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f128,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    k2_funct_1(k5_relat_1(sK0,sK1)) != k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.19/0.48    inference(backward_demodulation,[],[f36,f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f37,f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    v1_relat_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) & v2_funct_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f7])).
% 0.19/0.48  fof(f7,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) & (v2_funct_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,negated_conjecture,(
% 0.19/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 0.19/0.48    inference(negated_conjecture,[],[f5])).
% 0.19/0.48  fof(f5,conjecture,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0))) )),
% 0.19/0.48    inference(resolution,[],[f23,f16])).
% 0.19/0.48  % (30836)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    v1_relat_1(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0))),
% 0.19/0.48    inference(backward_demodulation,[],[f33,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.19/0.48    inference(subsumption_resolution,[],[f34,f16])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.19/0.48    inference(subsumption_resolution,[],[f30,f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    v1_funct_1(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.19/0.48    inference(resolution,[],[f24,f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    v2_funct_1(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k4_relat_1(sK0))),
% 0.19/0.48    inference(backward_demodulation,[],[f20,f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f31,f21])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.19/0.48    inference(subsumption_resolution,[],[f29,f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    v1_funct_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.19/0.48    inference(resolution,[],[f24,f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    v2_funct_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f128,plain,(
% 0.19/0.48    k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.19/0.48    inference(subsumption_resolution,[],[f127,f21])).
% 0.19/0.48  fof(f127,plain,(
% 0.19/0.48    ~v1_relat_1(sK0) | k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.19/0.48    inference(subsumption_resolution,[],[f119,f22])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f100,f18])).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    ( ! [X6] : (~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k4_relat_1(k5_relat_1(X6,sK1)) = k2_funct_1(k5_relat_1(X6,sK1))) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f99,f17])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    ( ! [X6] : (~v2_funct_1(X6) | ~v1_funct_1(sK1) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k4_relat_1(k5_relat_1(X6,sK1)) = k2_funct_1(k5_relat_1(X6,sK1))) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f90,f16])).
% 0.19/0.48  fof(f90,plain,(
% 0.19/0.48    ( ! [X6] : (~v2_funct_1(X6) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k4_relat_1(k5_relat_1(X6,sK1)) = k2_funct_1(k5_relat_1(X6,sK1))) )),
% 0.19/0.48    inference(resolution,[],[f73,f19])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1))) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f72,f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1))) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f65,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1))) )),
% 0.19/0.48    inference(resolution,[],[f26,f24])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (30845)------------------------------
% 0.19/0.48  % (30845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (30845)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (30845)Memory used [KB]: 6268
% 0.19/0.48  % (30845)Time elapsed: 0.069 s
% 0.19/0.48  % (30845)------------------------------
% 0.19/0.48  % (30845)------------------------------
% 0.19/0.48  % (30831)Success in time 0.124 s
%------------------------------------------------------------------------------
