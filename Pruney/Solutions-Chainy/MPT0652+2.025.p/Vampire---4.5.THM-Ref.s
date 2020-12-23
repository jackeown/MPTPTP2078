%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 165 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 532 expanded)
%              Number of equality atoms :   63 ( 209 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f110,f145])).

fof(f145,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f61,f142])).

fof(f142,plain,(
    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f140,f67])).

fof(f67,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(superposition,[],[f56,f47])).

fof(f47,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(resolution,[],[f37,f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f140,plain,(
    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f136,f25])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f131,f52])).

fof(f52,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k2_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f71,f25])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(k4_relat_1(X2),X1)) = k9_relat_1(X1,k2_relat_1(k4_relat_1(X2))) ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f61,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_1 ),
    inference(backward_demodulation,[],[f40,f59])).

fof(f59,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_subsumption,[],[f25,f26,f58])).

fof(f58,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f110,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f91,f106])).

fof(f106,plain,(
    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f105,f50])).

fof(f50,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f32,f25])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f103,f52])).

fof(f103,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f55,f25])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k2_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f31,f28])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f91,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | spl1_2 ),
    inference(superposition,[],[f60,f86])).

fof(f86,plain,(
    k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f74,f25])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) = k10_relat_1(k4_relat_1(X0),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f62,f28])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK0)) = k10_relat_1(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f60,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_2 ),
    inference(backward_demodulation,[],[f43,f59])).

fof(f43,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f24,f42,f39])).

fof(f24,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (2688)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (2688)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (2696)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f44,f110,f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl1_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    $false | spl1_1),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k2_relat_1(sK0) | spl1_1),
% 0.21/0.48    inference(superposition,[],[f61,f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f140,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.48    inference(superposition,[],[f56,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f30,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f37,f25])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f136,f25])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f131,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f33,f25])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k2_relat_1(k4_relat_1(sK0)))) )),
% 0.21/0.48    inference(resolution,[],[f71,f25])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(k4_relat_1(X2),X1)) = k9_relat_1(X1,k2_relat_1(k4_relat_1(X2)))) )),
% 0.21/0.48    inference(resolution,[],[f35,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_1),
% 0.21/0.48    inference(backward_demodulation,[],[f40,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.48    inference(global_subsumption,[],[f25,f26,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f36,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v2_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl1_1 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl1_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    $false | spl1_2),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k2_relat_1(sK0) | spl1_2),
% 0.21/0.48    inference(superposition,[],[f91,f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f105,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f32,f25])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f103,f52])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))),
% 0.21/0.48    inference(resolution,[],[f55,f25])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k2_relat_1(k4_relat_1(X0)))) )),
% 0.21/0.48    inference(resolution,[],[f31,f28])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | spl1_2),
% 0.21/0.48    inference(superposition,[],[f60,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f74,f25])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) = k10_relat_1(k4_relat_1(X0),k1_relat_1(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f62,f28])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK0)) = k10_relat_1(X0,k1_relat_1(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f34,f25])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_2),
% 0.21/0.48    inference(backward_demodulation,[],[f43,f59])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl1_2 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~spl1_1 | ~spl1_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f42,f39])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2688)------------------------------
% 0.21/0.48  % (2688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2688)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2688)Memory used [KB]: 10746
% 0.21/0.48  % (2688)Time elapsed: 0.057 s
% 0.21/0.48  % (2688)------------------------------
% 0.21/0.48  % (2688)------------------------------
% 0.21/0.48  % (2675)Success in time 0.125 s
%------------------------------------------------------------------------------
