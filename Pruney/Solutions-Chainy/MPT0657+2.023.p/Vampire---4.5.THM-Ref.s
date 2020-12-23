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
% DateTime   : Thu Dec  3 12:53:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 300 expanded)
%              Number of leaves         :    8 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 (2197 expanded)
%              Number of equality atoms :   68 ( 847 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21317)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f119,plain,(
    $false ),
    inference(global_subsumption,[],[f28,f118])).

fof(f118,plain,(
    k2_funct_1(sK0) = sK1 ),
    inference(forward_demodulation,[],[f117,f100])).

fof(f100,plain,(
    sK1 = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f97,f99])).

fof(f99,plain,(
    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f98,f44])).

fof(f44,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f98,plain,(
    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f87,f66])).

fof(f66,plain,(
    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f60,f26])).

fof(f26,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f25,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f25,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f23,f21,f42,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f42,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f97,plain,(
    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f96,f65])).

fof(f65,plain,(
    k5_relat_1(sK1,sK0) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(forward_demodulation,[],[f61,f27])).

fof(f27,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f21,f22,f25,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f88,f66])).

fof(f88,plain,(
    k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f42,f21,f42,f30])).

fof(f117,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f67,f64])).

fof(f64,plain,(
    k2_relat_1(sK1) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f63,f26])).

fof(f63,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f25,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f67,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f42,f29])).

fof(f28,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (21309)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (21315)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (21316)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (21307)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (21308)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (21316)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (21310)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (21317)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(global_subsumption,[],[f28,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    k2_funct_1(sK0) = sK1),
% 0.21/0.50    inference(forward_demodulation,[],[f117,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    sK1 = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.50    inference(backward_demodulation,[],[f97,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f98,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f23,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f87,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f60,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f21,f22,f25,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v2_funct_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    v1_funct_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f23,f21,f42,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f21,f22,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.50    inference(forward_demodulation,[],[f96,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    k5_relat_1(sK1,sK0) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f61,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f21,f22,f25,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.50    inference(forward_demodulation,[],[f88,f66])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),k2_funct_1(sK0)) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f42,f21,f42,f30])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.50    inference(forward_demodulation,[],[f67,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    k2_relat_1(sK1) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f63,f26])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f21,f22,f25,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f42,f29])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    k2_funct_1(sK0) != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (21316)------------------------------
% 0.21/0.50  % (21316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21316)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (21316)Memory used [KB]: 10618
% 0.21/0.50  % (21316)Time elapsed: 0.066 s
% 0.21/0.50  % (21316)------------------------------
% 0.21/0.50  % (21316)------------------------------
% 0.21/0.50  % (21304)Success in time 0.14 s
%------------------------------------------------------------------------------
