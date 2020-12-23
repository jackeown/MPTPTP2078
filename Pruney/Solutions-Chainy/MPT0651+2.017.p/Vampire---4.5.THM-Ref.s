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
% DateTime   : Thu Dec  3 12:52:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 239 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  144 ( 845 expanded)
%              Number of equality atoms :   55 ( 307 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f103,f114])).

fof(f114,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f51,f100])).

fof(f100,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f99,f45])).

fof(f45,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f99,plain,(
    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f98,f41])).

fof(f41,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f98,plain,(
    k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(global_subsumption,[],[f22,f23,f54])).

fof(f54,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f31,f50])).

fof(f50,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_subsumption,[],[f22,f23,f49])).

fof(f49,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f51,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_2 ),
    inference(backward_demodulation,[],[f39,f50])).

fof(f39,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f103,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f52,f91])).

fof(f91,plain,(
    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f90,f62])).

fof(f62,plain,(
    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f61,f43])).

fof(f43,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f57,f41])).

fof(f57,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f90,plain,(
    k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f70,f56])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f29,f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f52,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_1 ),
    inference(backward_demodulation,[],[f36,f50])).

fof(f36,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f40,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f21,f38,f35])).

fof(f21,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (9071)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (9071)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (9079)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f40,f103,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl1_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    $false | spl1_2),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f112])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    k1_relat_1(sK0) != k1_relat_1(sK0) | spl1_2),
% 0.20/0.47    inference(superposition,[],[f51,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f99,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.20/0.47    inference(resolution,[],[f25,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f98,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f27,f22])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f78,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(global_subsumption,[],[f22,f23,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.20/0.48    inference(superposition,[],[f31,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.48    inference(global_subsumption,[],[f22,f23,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.48    inference(resolution,[],[f33,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v2_funct_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v1_funct_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0))) )),
% 0.20/0.48    inference(resolution,[],[f30,f22])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_2),
% 0.20/0.48    inference(backward_demodulation,[],[f39,f50])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    spl1_2 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl1_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    $false | spl1_1),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(sK0) | spl1_1),
% 0.20/0.48    inference(superposition,[],[f52,f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f90,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f61,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f28,f22])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f57,f41])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f56,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f70,f56])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0))) )),
% 0.20/0.48    inference(resolution,[],[f29,f22])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_1),
% 0.20/0.48    inference(backward_demodulation,[],[f36,f50])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl1_1 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~spl1_1 | ~spl1_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f38,f35])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9071)------------------------------
% 0.20/0.48  % (9071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9071)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9071)Memory used [KB]: 10618
% 0.20/0.48  % (9071)Time elapsed: 0.064 s
% 0.20/0.48  % (9071)------------------------------
% 0.20/0.48  % (9071)------------------------------
% 0.20/0.48  % (9058)Success in time 0.122 s
%------------------------------------------------------------------------------
