%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:04 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 151 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 753 expanded)
%              Number of equality atoms :   58 ( 265 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1824,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1823,f37])).

fof(f37,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f1823,plain,(
    sK1 = k2_funct_1(sK0) ),
    inference(backward_demodulation,[],[f164,f1822])).

fof(f1822,plain,(
    sK1 = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1798,f224])).

fof(f224,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f223,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f223,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f222,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f222,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f221,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f221,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f220,f32])).

fof(f220,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1))) ),
    inference(superposition,[],[f46,f58])).

fof(f58,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f1798,plain,(
    k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f657,f32])).

fof(f657,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X9)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X9) ) ),
    inference(forward_demodulation,[],[f653,f91])).

fof(f91,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f90,f35])).

fof(f35,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f89,f39])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f83,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(resolution,[],[f34,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f34,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f653,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X9) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X9)) ) ),
    inference(resolution,[],[f104,f124])).

fof(f124,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f122,f38])).

fof(f122,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f104,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(X6,sK0),X7) = k5_relat_1(X6,k5_relat_1(sK0,X7)) ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f164,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f163,f36])).

fof(f36,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f163,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f144,f96])).

fof(f96,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,
    ( ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f34,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f144,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    inference(resolution,[],[f124,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (4860)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (4866)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (4871)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (4857)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (4851)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (4867)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (4862)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (4855)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (4863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4871)Refutation not found, incomplete strategy% (4871)------------------------------
% 0.21/0.52  % (4871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4870)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (4871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4871)Memory used [KB]: 10618
% 0.21/0.53  % (4871)Time elapsed: 0.091 s
% 0.21/0.53  % (4871)------------------------------
% 0.21/0.53  % (4871)------------------------------
% 0.21/0.53  % (4853)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (4856)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (4865)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.54  % (4861)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.54  % (4854)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (4852)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (4864)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.55  % (4858)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.55  % (4859)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.56  % (4868)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.56  % (4869)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 2.33/0.68  % (4864)Refutation found. Thanks to Tanya!
% 2.33/0.68  % SZS status Theorem for theBenchmark
% 2.33/0.68  % SZS output start Proof for theBenchmark
% 2.33/0.68  fof(f1824,plain,(
% 2.33/0.68    $false),
% 2.33/0.68    inference(subsumption_resolution,[],[f1823,f37])).
% 2.33/0.68  fof(f37,plain,(
% 2.33/0.68    sK1 != k2_funct_1(sK0)),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f16,plain,(
% 2.33/0.68    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.33/0.68    inference(flattening,[],[f15])).
% 2.33/0.68  fof(f15,plain,(
% 2.33/0.68    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.33/0.68    inference(ennf_transformation,[],[f14])).
% 2.33/0.68  fof(f14,negated_conjecture,(
% 2.33/0.68    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.33/0.68    inference(negated_conjecture,[],[f13])).
% 2.33/0.68  fof(f13,conjecture,(
% 2.33/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 2.33/0.68  fof(f1823,plain,(
% 2.33/0.68    sK1 = k2_funct_1(sK0)),
% 2.33/0.68    inference(backward_demodulation,[],[f164,f1822])).
% 2.33/0.68  fof(f1822,plain,(
% 2.33/0.68    sK1 = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))),
% 2.33/0.68    inference(forward_demodulation,[],[f1798,f224])).
% 2.33/0.68  fof(f224,plain,(
% 2.33/0.68    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 2.33/0.68    inference(subsumption_resolution,[],[f223,f32])).
% 2.33/0.68  fof(f32,plain,(
% 2.33/0.68    v1_relat_1(sK1)),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f223,plain,(
% 2.33/0.68    ~v1_relat_1(sK1) | sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 2.33/0.68    inference(resolution,[],[f222,f55])).
% 2.33/0.68  fof(f55,plain,(
% 2.33/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 2.33/0.68    inference(cnf_transformation,[],[f29])).
% 2.33/0.68  fof(f29,plain,(
% 2.33/0.68    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.33/0.68    inference(flattening,[],[f28])).
% 2.33/0.68  fof(f28,plain,(
% 2.33/0.68    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.33/0.68    inference(ennf_transformation,[],[f7])).
% 2.33/0.68  fof(f7,axiom,(
% 2.33/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 2.33/0.68  fof(f222,plain,(
% 2.33/0.68    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 2.33/0.68    inference(subsumption_resolution,[],[f221,f40])).
% 2.33/0.68  fof(f40,plain,(
% 2.33/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f10])).
% 2.33/0.68  fof(f10,axiom,(
% 2.33/0.68    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.33/0.68  fof(f221,plain,(
% 2.33/0.68    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1)))),
% 2.33/0.68    inference(subsumption_resolution,[],[f220,f32])).
% 2.33/0.68  fof(f220,plain,(
% 2.33/0.68    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1)))),
% 2.33/0.68    inference(superposition,[],[f46,f58])).
% 2.33/0.68  fof(f58,plain,(
% 2.33/0.68    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 2.33/0.68    inference(resolution,[],[f32,f45])).
% 2.33/0.68  fof(f45,plain,(
% 2.33/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.33/0.68    inference(cnf_transformation,[],[f18])).
% 2.33/0.68  fof(f18,plain,(
% 2.33/0.68    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.33/0.68    inference(ennf_transformation,[],[f8])).
% 2.33/0.68  fof(f8,axiom,(
% 2.33/0.68    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.33/0.68  fof(f46,plain,(
% 2.33/0.68    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f19])).
% 2.33/0.68  fof(f19,plain,(
% 2.33/0.68    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.33/0.68    inference(ennf_transformation,[],[f4])).
% 2.33/0.68  fof(f4,axiom,(
% 2.33/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 2.33/0.68  fof(f1798,plain,(
% 2.33/0.68    k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 2.33/0.68    inference(resolution,[],[f657,f32])).
% 2.33/0.68  fof(f657,plain,(
% 2.33/0.68    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X9)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X9)) )),
% 2.33/0.68    inference(forward_demodulation,[],[f653,f91])).
% 2.33/0.68  fof(f91,plain,(
% 2.33/0.68    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1))),
% 2.33/0.68    inference(forward_demodulation,[],[f90,f35])).
% 2.33/0.68  fof(f35,plain,(
% 2.33/0.68    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f90,plain,(
% 2.33/0.68    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 2.33/0.68    inference(subsumption_resolution,[],[f89,f39])).
% 2.33/0.68  fof(f39,plain,(
% 2.33/0.68    v1_funct_1(sK0)),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f89,plain,(
% 2.33/0.68    ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 2.33/0.68    inference(subsumption_resolution,[],[f83,f38])).
% 2.33/0.68  fof(f38,plain,(
% 2.33/0.68    v1_relat_1(sK0)),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f83,plain,(
% 2.33/0.68    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 2.33/0.68    inference(resolution,[],[f34,f54])).
% 2.33/0.68  fof(f54,plain,(
% 2.33/0.68    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 2.33/0.68    inference(cnf_transformation,[],[f27])).
% 2.33/0.68  fof(f27,plain,(
% 2.33/0.68    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.68    inference(flattening,[],[f26])).
% 2.33/0.68  fof(f26,plain,(
% 2.33/0.68    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.68    inference(ennf_transformation,[],[f12])).
% 2.33/0.68  fof(f12,axiom,(
% 2.33/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.33/0.68  fof(f34,plain,(
% 2.33/0.68    v2_funct_1(sK0)),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f653,plain,(
% 2.33/0.68    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X9) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X9))) )),
% 2.33/0.68    inference(resolution,[],[f104,f124])).
% 2.33/0.68  fof(f124,plain,(
% 2.33/0.68    v1_relat_1(k2_funct_1(sK0))),
% 2.33/0.68    inference(subsumption_resolution,[],[f122,f38])).
% 2.33/0.68  fof(f122,plain,(
% 2.33/0.68    ~v1_relat_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 2.33/0.68    inference(resolution,[],[f39,f49])).
% 2.33/0.68  fof(f49,plain,(
% 2.33/0.68    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f23])).
% 2.33/0.68  fof(f23,plain,(
% 2.33/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.68    inference(flattening,[],[f22])).
% 2.33/0.68  fof(f22,plain,(
% 2.33/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.68    inference(ennf_transformation,[],[f9])).
% 2.33/0.68  fof(f9,axiom,(
% 2.33/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.33/0.68  fof(f104,plain,(
% 2.33/0.68    ( ! [X6,X7] : (~v1_relat_1(X6) | ~v1_relat_1(X7) | k5_relat_1(k5_relat_1(X6,sK0),X7) = k5_relat_1(X6,k5_relat_1(sK0,X7))) )),
% 2.33/0.68    inference(resolution,[],[f38,f48])).
% 2.33/0.68  fof(f48,plain,(
% 2.33/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f21])).
% 2.33/0.68  fof(f21,plain,(
% 2.33/0.68    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.33/0.68    inference(ennf_transformation,[],[f5])).
% 2.33/0.68  fof(f5,axiom,(
% 2.33/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.33/0.68  fof(f164,plain,(
% 2.33/0.68    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))),
% 2.33/0.68    inference(forward_demodulation,[],[f163,f36])).
% 2.33/0.68  fof(f36,plain,(
% 2.33/0.68    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 2.33/0.68    inference(cnf_transformation,[],[f16])).
% 2.33/0.68  fof(f163,plain,(
% 2.33/0.68    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 2.33/0.68    inference(forward_demodulation,[],[f144,f96])).
% 2.33/0.68  fof(f96,plain,(
% 2.33/0.68    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 2.33/0.68    inference(subsumption_resolution,[],[f95,f39])).
% 2.33/0.68  fof(f95,plain,(
% 2.33/0.68    ~v1_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 2.33/0.68    inference(subsumption_resolution,[],[f85,f38])).
% 2.33/0.68  fof(f85,plain,(
% 2.33/0.68    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 2.33/0.68    inference(resolution,[],[f34,f52])).
% 2.33/0.68  fof(f52,plain,(
% 2.33/0.68    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 2.33/0.68    inference(cnf_transformation,[],[f25])).
% 2.33/0.68  fof(f25,plain,(
% 2.33/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.68    inference(flattening,[],[f24])).
% 2.33/0.68  fof(f24,plain,(
% 2.33/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.68    inference(ennf_transformation,[],[f11])).
% 2.33/0.68  fof(f11,axiom,(
% 2.33/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.33/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.33/0.68  fof(f144,plain,(
% 2.33/0.68    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 2.33/0.68    inference(resolution,[],[f124,f45])).
% 2.33/0.68  % SZS output end Proof for theBenchmark
% 2.33/0.68  % (4864)------------------------------
% 2.33/0.68  % (4864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.68  % (4864)Termination reason: Refutation
% 2.33/0.68  
% 2.33/0.68  % (4864)Memory used [KB]: 2942
% 2.33/0.68  % (4864)Time elapsed: 0.251 s
% 2.33/0.68  % (4864)------------------------------
% 2.33/0.68  % (4864)------------------------------
% 2.33/0.69  % (4850)Success in time 0.32 s
%------------------------------------------------------------------------------
