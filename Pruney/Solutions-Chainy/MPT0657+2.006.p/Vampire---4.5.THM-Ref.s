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
% DateTime   : Thu Dec  3 12:53:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 503 expanded)
%              Number of leaves         :   13 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  275 (2512 expanded)
%              Number of equality atoms :  112 ( 963 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1240,f166])).

fof(f166,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f41,f109])).

fof(f109,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f108,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f107,f43])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f41,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1240,plain,(
    sK1 = k4_relat_1(sK0) ),
    inference(backward_demodulation,[],[f1190,f1235])).

fof(f1235,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f1198,f1199])).

fof(f1199,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f589,f1198])).

fof(f589,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)
    | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f588,f275])).

fof(f275,plain,(
    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f274,f88])).

fof(f88,plain,(
    k2_relat_1(sK1) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f86,f39])).

fof(f39,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f274,plain,(
    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f263,f243])).

fof(f243,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f85,f242])).

fof(f242,plain,(
    k2_relat_1(sK0) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f241,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f241,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f240,f40])).

fof(f40,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f240,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f232,f39])).

fof(f232,plain,(
    k1_relat_1(k5_relat_1(sK1,sK0)) = k10_relat_1(sK1,k1_relat_1(sK0)) ),
    inference(resolution,[],[f118,f42])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f85,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f47,f36])).

fof(f263,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f119,f36])).

fof(f119,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(sK0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f51,f42])).

fof(f588,plain,
    ( sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f587,f275])).

fof(f587,plain,
    ( k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f579,f192])).

fof(f192,plain,(
    v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f83,f36])).

fof(f83,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f579,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f211,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(k1_relat_1(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f135,f36])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | sK1 != k5_relat_1(sK1,X0)
      | k6_relat_1(k1_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f211,plain,(
    v1_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f206,f36])).

fof(f206,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f117,f37])).

fof(f117,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(k5_relat_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f1198,plain,(
    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1186,f247])).

fof(f247,plain,(
    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(backward_demodulation,[],[f91,f243])).

fof(f91,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1186,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f283,f36])).

fof(f283,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(sK1,k5_relat_1(sK0,X5)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X5) ) ),
    inference(forward_demodulation,[],[f281,f40])).

fof(f281,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(sK1,sK0),X5) = k5_relat_1(sK1,k5_relat_1(sK0,X5)) ) ),
    inference(resolution,[],[f131,f42])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1190,plain,(
    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1189,f102])).

fof(f102,plain,(
    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f96,f74])).

fof(f74,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f96,plain,(
    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0)) ),
    inference(resolution,[],[f63,f48])).

fof(f63,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f46,f42])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f1189,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1169,f126])).

fof(f126,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f125,f39])).

fof(f125,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f124,f109])).

fof(f124,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f123,f42])).

fof(f123,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f122,f43])).

fof(f122,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1169,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f283,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (8779)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (8787)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (8787)Refutation not found, incomplete strategy% (8787)------------------------------
% 0.21/0.47  % (8787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (8787)Memory used [KB]: 10618
% 0.21/0.47  % (8787)Time elapsed: 0.066 s
% 0.21/0.47  % (8787)------------------------------
% 0.21/0.47  % (8787)------------------------------
% 0.21/0.47  % (8767)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (8769)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (8778)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (8776)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (8781)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (8772)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8773)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (8777)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (8771)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (8768)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8782)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (8770)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (8780)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (8783)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (8775)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (8786)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (8785)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (8774)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (8784)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.57  % (8784)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1241,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f1240,f166])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    sK1 != k4_relat_1(sK0)),
% 0.21/0.57    inference(superposition,[],[f41,f109])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f108,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    v1_relat_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.57    inference(negated_conjecture,[],[f14])).
% 0.21/0.57  fof(f14,conjecture,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f107,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    v1_funct_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.57    inference(resolution,[],[f55,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    v2_funct_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    sK1 != k2_funct_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f1240,plain,(
% 0.21/0.57    sK1 = k4_relat_1(sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f1190,f1235])).
% 0.21/0.57  fof(f1235,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.57    inference(backward_demodulation,[],[f1198,f1199])).
% 0.21/0.57  fof(f1199,plain,(
% 0.21/0.57    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f589,f1198])).
% 0.21/0.57  fof(f589,plain,(
% 0.21/0.57    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f588,f275])).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f274,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    k2_relat_1(sK1) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f86,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f47,f42])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.57  fof(f274,plain,(
% 0.21/0.57    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f263,f243])).
% 0.21/0.57  fof(f243,plain,(
% 0.21/0.57    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f85,f242])).
% 0.21/0.57  fof(f242,plain,(
% 0.21/0.57    k2_relat_1(sK0) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f241,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.57  fof(f241,plain,(
% 0.21/0.57    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.57    inference(forward_demodulation,[],[f240,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f232,f39])).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    k1_relat_1(k5_relat_1(sK1,sK0)) = k10_relat_1(sK1,k1_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f118,f42])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0))) )),
% 0.21/0.57    inference(resolution,[],[f51,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.57    inference(resolution,[],[f47,f36])).
% 0.21/0.57  fof(f263,plain,(
% 0.21/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.21/0.57    inference(resolution,[],[f119,f36])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(sK0,k1_relat_1(X1))) )),
% 0.21/0.57    inference(resolution,[],[f51,f42])).
% 0.21/0.57  fof(f588,plain,(
% 0.21/0.57    sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f587,f275])).
% 0.21/0.57  fof(f587,plain,(
% 0.21/0.57    k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1)) | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f579,f192])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(resolution,[],[f83,f36])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(sK0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f61,f42])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    ~v1_relat_1(k5_relat_1(sK0,sK1)) | k2_relat_1(sK1) != k1_relat_1(k5_relat_1(sK0,sK1)) | sK1 != k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.21/0.57    inference(resolution,[],[f211,f137])).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k1_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f135,f36])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k1_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(resolution,[],[f58,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    v1_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    v1_funct_1(k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(subsumption_resolution,[],[f206,f36])).
% 0.21/0.57  fof(f206,plain,(
% 0.21/0.57    ~v1_relat_1(sK1) | v1_funct_1(k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(resolution,[],[f117,f37])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_1(k5_relat_1(sK0,X1))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f115,f42])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(sK0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f60,f43])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.21/0.57  fof(f1198,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f1186,f247])).
% 0.21/0.57  fof(f247,plain,(
% 0.21/0.57    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f91,f243])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.21/0.57    inference(resolution,[],[f48,f36])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.57  fof(f1186,plain,(
% 0.21/0.57    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.21/0.57    inference(resolution,[],[f283,f36])).
% 0.21/0.57  fof(f283,plain,(
% 0.21/0.57    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(sK1,k5_relat_1(sK0,X5)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X5)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f281,f40])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(sK1,sK0),X5) = k5_relat_1(sK1,k5_relat_1(sK0,X5))) )),
% 0.21/0.57    inference(resolution,[],[f131,f42])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f52,f36])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.57  fof(f1190,plain,(
% 0.21/0.57    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.57    inference(forward_demodulation,[],[f1189,f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f96,f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f49,f42])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f63,f48])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f46,f42])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.57  fof(f1189,plain,(
% 0.21/0.57    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.57    inference(forward_demodulation,[],[f1169,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f125,f39])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f124,f109])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f123,f42])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f43])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f56,f38])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.57  fof(f1169,plain,(
% 0.21/0.57    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.57    inference(resolution,[],[f283,f63])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (8784)------------------------------
% 0.21/0.57  % (8784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8784)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (8784)Memory used [KB]: 2686
% 0.21/0.57  % (8784)Time elapsed: 0.174 s
% 0.21/0.57  % (8784)------------------------------
% 0.21/0.57  % (8784)------------------------------
% 0.21/0.57  % (8766)Success in time 0.223 s
%------------------------------------------------------------------------------
