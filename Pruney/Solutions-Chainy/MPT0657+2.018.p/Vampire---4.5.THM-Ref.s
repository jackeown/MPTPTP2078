%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 908 expanded)
%              Number of leaves         :   12 ( 166 expanded)
%              Depth                    :   29
%              Number of atoms          :  367 (4620 expanded)
%              Number of equality atoms :  121 (1633 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1571,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1570,f37])).

fof(f37,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1570,plain,(
    sK1 = k2_funct_1(sK0) ),
    inference(forward_demodulation,[],[f1508,f710])).

fof(f710,plain,(
    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f702,f374])).

fof(f374,plain,(
    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),sK1) ),
    inference(forward_demodulation,[],[f371,f36])).

fof(f36,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f371,plain,(
    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(backward_demodulation,[],[f57,f367])).

fof(f367,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f56,f366])).

fof(f366,plain,(
    k2_relat_1(sK0) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f365,f201])).

fof(f201,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f365,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f359,f35])).

fof(f35,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f359,plain,(
    k1_relat_1(k5_relat_1(sK1,sK0)) = k10_relat_1(sK1,k1_relat_1(sK0)) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f57,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f702,plain,(
    k5_relat_1(k5_relat_1(sK1,sK0),sK1) = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f547,f32])).

fof(f547,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k5_relat_1(k5_relat_1(sK1,sK0),X14) = k5_relat_1(sK1,k5_relat_1(sK0,X14)) ) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(sK1,X2),X3) = k5_relat_1(sK1,k5_relat_1(X2,X3)) ) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1508,plain,(
    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f705,f1463])).

fof(f1463,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1462,f710])).

fof(f1462,plain,
    ( sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1461,f453])).

fof(f453,plain,(
    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f452,f129])).

fof(f129,plain,(
    k2_relat_1(sK1) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f108,f35])).

fof(f108,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f38,f42])).

fof(f452,plain,(
    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f444,f367])).

fof(f444,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f110,f32])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f38,f44])).

fof(f1461,plain,
    ( k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1454,f1329])).

fof(f1329,plain,(
    v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1328,f32])).

fof(f1328,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1322,f1087])).

fof(f1087,plain,(
    v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1086,f32])).

fof(f1086,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1084,f38])).

fof(f1084,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f1081,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1081,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1075,f38])).

fof(f1075,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f55,f1071])).

fof(f1071,plain,(
    k5_relat_1(sK0,k5_relat_1(sK1,sK0)) = k5_relat_1(k5_relat_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f602,f38])).

fof(f602,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k5_relat_1(k5_relat_1(sK0,sK1),X14) = k5_relat_1(sK0,k5_relat_1(sK1,X14)) ) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,sK1),X5) = k5_relat_1(X4,k5_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f32,f45])).

fof(f1322,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f55,f1237])).

fof(f1237,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)),sK1) ),
    inference(forward_demodulation,[],[f1221,f374])).

fof(f1221,plain,(
    k5_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)),sK1) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),sK1)) ),
    inference(resolution,[],[f690,f321])).

fof(f321,plain,(
    v1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f320,f38])).

fof(f320,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f314,f144])).

fof(f144,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f132,f38])).

fof(f132,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f314,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f55,f102])).

fof(f102,plain,(
    k5_relat_1(sK1,sK0) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(forward_demodulation,[],[f101,f36])).

fof(f101,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f100,f39])).

fof(f100,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f34,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f690,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k5_relat_1(k5_relat_1(sK0,X14),sK1) = k5_relat_1(sK0,k5_relat_1(X14,sK1)) ) ),
    inference(resolution,[],[f62,f38])).

fof(f62,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(X6,X7),sK1) = k5_relat_1(X6,k5_relat_1(X7,sK1)) ) ),
    inference(resolution,[],[f32,f45])).

fof(f1454,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) ),
    inference(resolution,[],[f1441,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(k2_relat_1(sK1)) = X0 ) ),
    inference(inner_rewriting,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(k1_relat_1(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f83,f32])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(k1_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f1441,plain,(
    v1_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1440,f389])).

fof(f389,plain,(
    v1_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f388,f39])).

fof(f388,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f387,f38])).

fof(f387,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f324,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f324,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | v1_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f323,f39])).

fof(f323,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f322,f38])).

fof(f322,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f316,f144])).

fof(f316,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(superposition,[],[f54,f102])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f1440,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f1439,f321])).

fof(f1439,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f1438,f39])).

fof(f1438,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f1437,f38])).

fof(f1437,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f1332,f54])).

fof(f1332,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | v1_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1331,f33])).

fof(f1331,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1330,f32])).

fof(f1330,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1324,f1087])).

fof(f1324,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f54,f1237])).

fof(f705,plain,(
    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f704,f196])).

fof(f196,plain,(
    k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f195,f36])).

fof(f195,plain,(
    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f173,f104])).

fof(f104,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f103,f39])).

fof(f103,plain,
    ( ~ v1_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f95,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f173,plain,(
    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) ),
    inference(resolution,[],[f144,f43])).

fof(f704,plain,(
    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f699,f99])).

fof(f99,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f98,f35])).

fof(f98,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f97,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f34,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f699,plain,(
    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(resolution,[],[f547,f144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (5232)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.44  % (5232)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f1571,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f1570,f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    sK1 != k2_funct_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.44    inference(negated_conjecture,[],[f12])).
% 0.20/0.44  fof(f12,conjecture,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.44  fof(f1570,plain,(
% 0.20/0.44    sK1 = k2_funct_1(sK0)),
% 0.20/0.44    inference(forward_demodulation,[],[f1508,f710])).
% 0.20/0.44  fof(f710,plain,(
% 0.20/0.44    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(forward_demodulation,[],[f702,f374])).
% 0.20/0.44  fof(f374,plain,(
% 0.20/0.44    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),sK1)),
% 0.20/0.44    inference(forward_demodulation,[],[f371,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f371,plain,(
% 0.20/0.44    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.20/0.44    inference(backward_demodulation,[],[f57,f367])).
% 0.20/0.44  fof(f367,plain,(
% 0.20/0.44    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.44    inference(backward_demodulation,[],[f56,f366])).
% 0.20/0.44  fof(f366,plain,(
% 0.20/0.44    k2_relat_1(sK0) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.20/0.44    inference(forward_demodulation,[],[f365,f201])).
% 0.20/0.44  fof(f201,plain,(
% 0.20/0.44    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(superposition,[],[f40,f36])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.44  fof(f365,plain,(
% 0.20/0.44    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(forward_demodulation,[],[f359,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f359,plain,(
% 0.20/0.44    k1_relat_1(k5_relat_1(sK1,sK0)) = k10_relat_1(sK1,k1_relat_1(sK0))),
% 0.20/0.44    inference(resolution,[],[f58,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    v1_relat_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0))) )),
% 0.20/0.44    inference(resolution,[],[f32,f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    v1_relat_1(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 0.20/0.44    inference(resolution,[],[f32,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.44    inference(resolution,[],[f32,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.44  fof(f702,plain,(
% 0.20/0.44    k5_relat_1(k5_relat_1(sK1,sK0),sK1) = k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(resolution,[],[f547,f32])).
% 0.20/0.44  fof(f547,plain,(
% 0.20/0.44    ( ! [X14] : (~v1_relat_1(X14) | k5_relat_1(k5_relat_1(sK1,sK0),X14) = k5_relat_1(sK1,k5_relat_1(sK0,X14))) )),
% 0.20/0.44    inference(resolution,[],[f60,f38])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(sK1,X2),X3) = k5_relat_1(sK1,k5_relat_1(X2,X3))) )),
% 0.20/0.44    inference(resolution,[],[f32,f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.44  fof(f1508,plain,(
% 0.20/0.44    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(backward_demodulation,[],[f705,f1463])).
% 0.20/0.44  fof(f1463,plain,(
% 0.20/0.44    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1462,f710])).
% 0.20/0.44  fof(f1462,plain,(
% 0.20/0.44    sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1461,f453])).
% 0.20/0.44  fof(f453,plain,(
% 0.20/0.44    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(forward_demodulation,[],[f452,f129])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    k2_relat_1(sK1) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.20/0.44    inference(forward_demodulation,[],[f108,f35])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.20/0.44    inference(resolution,[],[f38,f42])).
% 0.20/0.44  fof(f452,plain,(
% 0.20/0.44    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(forward_demodulation,[],[f444,f367])).
% 0.20/0.44  fof(f444,plain,(
% 0.20/0.44    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.20/0.44    inference(resolution,[],[f110,f32])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0))) )),
% 0.20/0.44    inference(resolution,[],[f38,f44])).
% 0.20/0.44  fof(f1461,plain,(
% 0.20/0.44    k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1)) | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1454,f1329])).
% 0.20/0.44  fof(f1329,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1328,f32])).
% 0.20/0.44  fof(f1328,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1322,f1087])).
% 0.20/0.44  fof(f1087,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1086,f32])).
% 0.20/0.44  fof(f1086,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1084,f38])).
% 0.20/0.44  fof(f1084,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.20/0.44    inference(resolution,[],[f1081,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.44  fof(f1081,plain,(
% 0.20/0.44    ~v1_relat_1(k5_relat_1(sK0,sK1)) | v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1075,f38])).
% 0.20/0.44  fof(f1075,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.20/0.44    inference(superposition,[],[f55,f1071])).
% 0.20/0.44  fof(f1071,plain,(
% 0.20/0.44    k5_relat_1(sK0,k5_relat_1(sK1,sK0)) = k5_relat_1(k5_relat_1(sK0,sK1),sK0)),
% 0.20/0.44    inference(resolution,[],[f602,f38])).
% 0.20/0.44  fof(f602,plain,(
% 0.20/0.44    ( ! [X14] : (~v1_relat_1(X14) | k5_relat_1(k5_relat_1(sK0,sK1),X14) = k5_relat_1(sK0,k5_relat_1(sK1,X14))) )),
% 0.20/0.44    inference(resolution,[],[f61,f38])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,sK1),X5) = k5_relat_1(X4,k5_relat_1(sK1,X5))) )),
% 0.20/0.44    inference(resolution,[],[f32,f45])).
% 0.20/0.44  fof(f1322,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 0.20/0.44    inference(superposition,[],[f55,f1237])).
% 0.20/0.44  fof(f1237,plain,(
% 0.20/0.44    k5_relat_1(sK0,sK1) = k5_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)),sK1)),
% 0.20/0.44    inference(forward_demodulation,[],[f1221,f374])).
% 0.20/0.44  fof(f1221,plain,(
% 0.20/0.44    k5_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)),sK1) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),sK1))),
% 0.20/0.44    inference(resolution,[],[f690,f321])).
% 0.20/0.44  fof(f321,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f320,f38])).
% 0.20/0.44  fof(f320,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f314,f144])).
% 0.20/0.44  fof(f144,plain,(
% 0.20/0.44    v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f132,f38])).
% 0.20/0.44  fof(f132,plain,(
% 0.20/0.44    ~v1_relat_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.44    inference(resolution,[],[f39,f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    v1_funct_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f314,plain,(
% 0.20/0.44    v1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.20/0.44    inference(superposition,[],[f55,f102])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    k5_relat_1(sK1,sK0) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.44    inference(forward_demodulation,[],[f101,f36])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f100,f39])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f94,f38])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.44    inference(resolution,[],[f34,f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    v2_funct_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f690,plain,(
% 0.20/0.44    ( ! [X14] : (~v1_relat_1(X14) | k5_relat_1(k5_relat_1(sK0,X14),sK1) = k5_relat_1(sK0,k5_relat_1(X14,sK1))) )),
% 0.20/0.44    inference(resolution,[],[f62,f38])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    ( ! [X6,X7] : (~v1_relat_1(X6) | ~v1_relat_1(X7) | k5_relat_1(k5_relat_1(X6,X7),sK1) = k5_relat_1(X6,k5_relat_1(X7,sK1))) )),
% 0.20/0.44    inference(resolution,[],[f32,f45])).
% 0.20/0.44  fof(f1454,plain,(
% 0.20/0.44    ~v1_relat_1(k5_relat_1(sK0,sK1)) | k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1)) | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)),
% 0.20/0.44    inference(resolution,[],[f1441,f91])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k2_relat_1(sK1)) = X0) )),
% 0.20/0.44    inference(inner_rewriting,[],[f90])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k1_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f83,f32])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k1_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(resolution,[],[f33,f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    v1_funct_1(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f1441,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1440,f389])).
% 0.20/0.44  fof(f389,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f388,f39])).
% 0.20/0.44  fof(f388,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f387,f38])).
% 0.20/0.44  fof(f387,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.44    inference(resolution,[],[f324,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f324,plain,(
% 0.20/0.44    ~v1_funct_1(k2_funct_1(sK0)) | v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f323,f39])).
% 0.20/0.44  fof(f323,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f322,f38])).
% 0.20/0.44  fof(f322,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f316,f144])).
% 0.20/0.44  fof(f316,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.44    inference(superposition,[],[f54,f102])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.20/0.44  fof(f1440,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1439,f321])).
% 0.20/0.44  fof(f1439,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1438,f39])).
% 0.20/0.44  fof(f1438,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1437,f38])).
% 0.20/0.44  fof(f1437,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_funct_1(k5_relat_1(sK1,sK0))),
% 0.20/0.44    inference(resolution,[],[f1332,f54])).
% 0.20/0.44  fof(f1332,plain,(
% 0.20/0.44    ~v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | v1_funct_1(k5_relat_1(sK0,sK1))),
% 0.20/0.44    inference(subsumption_resolution,[],[f1331,f33])).
% 0.20/0.44  fof(f1331,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_funct_1(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1330,f32])).
% 0.20/0.44  fof(f1330,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1324,f1087])).
% 0.20/0.44  fof(f1324,plain,(
% 0.20/0.44    v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_funct_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.20/0.44    inference(superposition,[],[f54,f1237])).
% 0.20/0.44  fof(f705,plain,(
% 0.20/0.44    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.20/0.44    inference(forward_demodulation,[],[f704,f196])).
% 0.20/0.44  fof(f196,plain,(
% 0.20/0.44    k2_funct_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0))),
% 0.20/0.44    inference(forward_demodulation,[],[f195,f36])).
% 0.20/0.44  fof(f195,plain,(
% 0.20/0.44    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))),
% 0.20/0.44    inference(forward_demodulation,[],[f173,f104])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f103,f39])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    ~v1_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f95,f38])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.44    inference(resolution,[],[f34,f48])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.44  fof(f173,plain,(
% 0.20/0.44    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0))),
% 0.20/0.44    inference(resolution,[],[f144,f43])).
% 0.20/0.44  fof(f704,plain,(
% 0.20/0.44    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.20/0.44    inference(forward_demodulation,[],[f699,f99])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.44    inference(forward_demodulation,[],[f98,f35])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f97,f39])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f93,f38])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.44    inference(resolution,[],[f34,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f699,plain,(
% 0.20/0.44    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.44    inference(resolution,[],[f547,f144])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (5232)------------------------------
% 0.20/0.44  % (5232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (5232)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (5232)Memory used [KB]: 2558
% 0.20/0.44  % (5232)Time elapsed: 0.037 s
% 0.20/0.44  % (5232)------------------------------
% 0.20/0.44  % (5232)------------------------------
% 0.20/0.44  % (5218)Success in time 0.09 s
%------------------------------------------------------------------------------
