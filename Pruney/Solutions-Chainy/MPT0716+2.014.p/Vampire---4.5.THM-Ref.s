%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:50 EST 2020

% Result     : Theorem 17.84s
% Output     : Refutation 18.45s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 377 expanded)
%              Number of leaves         :   16 (  71 expanded)
%              Depth                    :   22
%              Number of atoms          :  268 (1672 expanded)
%              Number of equality atoms :   42 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13623,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13622,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f13622,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f13621,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f13621,plain,(
    ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f1433,f1485,f13620])).

fof(f13620,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f13615,f1503])).

fof(f1503,plain,(
    k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f709,f1491])).

fof(f1491,plain,(
    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1486,f44])).

fof(f1486,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f1485,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f709,plain,(
    ! [X22] : k9_relat_1(k7_relat_1(sK0,X22),k1_relat_1(k7_relat_1(sK0,X22))) = k9_relat_1(sK0,X22) ),
    inference(forward_demodulation,[],[f706,f79])).

fof(f79,plain,(
    ! [X8] : k2_relat_1(k7_relat_1(sK0,X8)) = k9_relat_1(sK0,X8) ),
    inference(resolution,[],[f53,f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f706,plain,(
    ! [X22] : k9_relat_1(k7_relat_1(sK0,X22),k1_relat_1(k7_relat_1(sK0,X22))) = k2_relat_1(k7_relat_1(sK0,X22)) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k7_relat_1(X2,X3),k1_relat_1(k7_relat_1(X2,X3))) = k2_relat_1(k7_relat_1(X2,X3)) ) ),
    inference(resolution,[],[f48,f51])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f13615,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f830,f1665])).

fof(f1665,plain,(
    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(subsumption_resolution,[],[f1664,f44])).

fof(f1664,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1663,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f1663,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1439,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1439,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f1434,f528])).

fof(f528,plain,(
    ! [X15] : k7_relat_1(k5_relat_1(sK0,sK1),X15) = k5_relat_1(k7_relat_1(sK0,X15),sK1) ),
    inference(resolution,[],[f457,f44])).

fof(f457,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(X13)
      | k7_relat_1(k5_relat_1(X13,sK1),X14) = k5_relat_1(k7_relat_1(X13,X14),sK1) ) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f1434,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1360,f54])).

fof(f1360,plain,(
    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f1359])).

fof(f1359,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1358,f162])).

fof(f162,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f134,f44])).

fof(f134,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k1_relat_1(k5_relat_1(X9,sK1)) = k10_relat_1(X9,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f50,f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1358,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1357,f40])).

fof(f40,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1357,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1356,f44])).

fof(f1356,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1306,f45])).

fof(f45,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f1306,plain,
    ( ~ v1_funct_1(sK0)
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f830,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1))
      | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f829,f115])).

fof(f115,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK0,X0)) ),
    inference(subsumption_resolution,[],[f114,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f114,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f112,f44])).

fof(f112,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f47,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f58,f72])).

fof(f72,plain,(
    ! [X8] : k7_relat_1(sK0,X8) = k5_relat_1(k6_relat_1(X8),sK0) ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f829,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1))
      | ~ v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(superposition,[],[f59,f826])).

fof(f826,plain,(
    ! [X32] : k1_relat_1(k5_relat_1(k7_relat_1(sK0,X32),sK1)) = k10_relat_1(k7_relat_1(sK0,X32),k1_relat_1(sK1)) ),
    inference(resolution,[],[f160,f44])).

fof(f160,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k5_relat_1(k7_relat_1(X2,X3),sK1)) = k10_relat_1(k7_relat_1(X2,X3),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f134,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f1485,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1484,f44])).

fof(f1484,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1481,f42])).

fof(f1481,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1479,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f1479,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f61,f1438])).

fof(f1438,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f1360,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1433,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f1360,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (21564)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (21560)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (21563)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (21578)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (21570)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (21571)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (21582)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (21574)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (21569)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (21581)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (21579)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (21558)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (21577)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (21573)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (21562)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (21562)Refutation not found, incomplete strategy% (21562)------------------------------
% 0.20/0.51  % (21562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21562)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21562)Memory used [KB]: 10618
% 0.20/0.51  % (21562)Time elapsed: 0.098 s
% 0.20/0.51  % (21562)------------------------------
% 0.20/0.51  % (21562)------------------------------
% 0.20/0.51  % (21565)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (21566)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (21572)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.52  % (21567)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (21561)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (21580)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (21575)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (21569)Refutation not found, incomplete strategy% (21569)------------------------------
% 0.20/0.52  % (21569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21569)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21569)Memory used [KB]: 10618
% 0.20/0.52  % (21569)Time elapsed: 0.113 s
% 0.20/0.52  % (21569)------------------------------
% 0.20/0.52  % (21569)------------------------------
% 0.20/0.52  % (21568)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (21583)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.54  % (21583)Refutation not found, incomplete strategy% (21583)------------------------------
% 0.20/0.54  % (21583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21583)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21583)Memory used [KB]: 10618
% 0.20/0.54  % (21583)Time elapsed: 0.127 s
% 0.20/0.54  % (21583)------------------------------
% 0.20/0.54  % (21583)------------------------------
% 1.76/0.62  % (21582)Refutation not found, incomplete strategy% (21582)------------------------------
% 1.76/0.62  % (21582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.63  % (21582)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.63  
% 1.76/0.63  % (21582)Memory used [KB]: 1663
% 1.76/0.63  % (21582)Time elapsed: 0.149 s
% 1.76/0.63  % (21582)------------------------------
% 1.76/0.63  % (21582)------------------------------
% 4.16/0.91  % (21571)Time limit reached!
% 4.16/0.91  % (21571)------------------------------
% 4.16/0.91  % (21571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.91  % (21571)Termination reason: Time limit
% 4.16/0.91  % (21571)Termination phase: Saturation
% 4.16/0.91  
% 4.16/0.91  % (21571)Memory used [KB]: 18038
% 4.16/0.91  % (21571)Time elapsed: 0.516 s
% 4.16/0.91  % (21571)------------------------------
% 4.16/0.91  % (21571)------------------------------
% 4.16/0.92  % (21566)Time limit reached!
% 4.16/0.92  % (21566)------------------------------
% 4.16/0.92  % (21566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.92  % (21566)Termination reason: Time limit
% 4.16/0.92  
% 4.16/0.92  % (21566)Memory used [KB]: 13048
% 4.16/0.92  % (21566)Time elapsed: 0.511 s
% 4.16/0.92  % (21566)------------------------------
% 4.16/0.92  % (21566)------------------------------
% 17.84/2.67  % (21572)Refutation found. Thanks to Tanya!
% 17.84/2.67  % SZS status Theorem for theBenchmark
% 17.84/2.67  % SZS output start Proof for theBenchmark
% 17.84/2.67  fof(f13623,plain,(
% 17.84/2.67    $false),
% 17.84/2.67    inference(subsumption_resolution,[],[f13622,f44])).
% 17.84/2.67  fof(f44,plain,(
% 17.84/2.67    v1_relat_1(sK0)),
% 17.84/2.67    inference(cnf_transformation,[],[f19])).
% 17.84/2.67  fof(f19,plain,(
% 17.84/2.67    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 17.84/2.67    inference(flattening,[],[f18])).
% 17.84/2.67  fof(f18,plain,(
% 17.84/2.67    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 17.84/2.67    inference(ennf_transformation,[],[f17])).
% 17.84/2.67  fof(f17,negated_conjecture,(
% 17.84/2.67    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 17.84/2.67    inference(negated_conjecture,[],[f16])).
% 17.84/2.67  fof(f16,conjecture,(
% 17.84/2.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 17.84/2.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 17.84/2.67  fof(f13622,plain,(
% 17.84/2.67    ~v1_relat_1(sK0)),
% 17.84/2.67    inference(resolution,[],[f13621,f51])).
% 17.84/2.67  fof(f51,plain,(
% 17.84/2.67    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 17.84/2.67    inference(cnf_transformation,[],[f23])).
% 17.84/2.67  fof(f23,plain,(
% 17.84/2.67    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 17.84/2.67    inference(ennf_transformation,[],[f4])).
% 17.84/2.67  fof(f4,axiom,(
% 17.84/2.67    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 17.84/2.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 18.45/2.68  fof(f13621,plain,(
% 18.45/2.68    ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 18.45/2.68    inference(global_subsumption,[],[f1433,f1485,f13620])).
% 18.45/2.68  fof(f13620,plain,(
% 18.45/2.68    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 18.45/2.68    inference(forward_demodulation,[],[f13615,f1503])).
% 18.45/2.68  fof(f1503,plain,(
% 18.45/2.68    k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK2),sK2)),
% 18.45/2.68    inference(superposition,[],[f709,f1491])).
% 18.45/2.68  fof(f1491,plain,(
% 18.45/2.68    sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 18.45/2.68    inference(subsumption_resolution,[],[f1486,f44])).
% 18.45/2.68  fof(f1486,plain,(
% 18.45/2.68    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 18.45/2.68    inference(resolution,[],[f1485,f54])).
% 18.45/2.68  fof(f54,plain,(
% 18.45/2.68    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 18.45/2.68    inference(cnf_transformation,[],[f27])).
% 18.45/2.68  fof(f27,plain,(
% 18.45/2.68    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 18.45/2.68    inference(flattening,[],[f26])).
% 18.45/2.68  fof(f26,plain,(
% 18.45/2.68    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 18.45/2.68    inference(ennf_transformation,[],[f10])).
% 18.45/2.68  fof(f10,axiom,(
% 18.45/2.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 18.45/2.68  fof(f709,plain,(
% 18.45/2.68    ( ! [X22] : (k9_relat_1(k7_relat_1(sK0,X22),k1_relat_1(k7_relat_1(sK0,X22))) = k9_relat_1(sK0,X22)) )),
% 18.45/2.68    inference(forward_demodulation,[],[f706,f79])).
% 18.45/2.68  fof(f79,plain,(
% 18.45/2.68    ( ! [X8] : (k2_relat_1(k7_relat_1(sK0,X8)) = k9_relat_1(sK0,X8)) )),
% 18.45/2.68    inference(resolution,[],[f53,f44])).
% 18.45/2.68  fof(f53,plain,(
% 18.45/2.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f25])).
% 18.45/2.68  fof(f25,plain,(
% 18.45/2.68    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 18.45/2.68    inference(ennf_transformation,[],[f7])).
% 18.45/2.68  fof(f7,axiom,(
% 18.45/2.68    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 18.45/2.68  fof(f706,plain,(
% 18.45/2.68    ( ! [X22] : (k9_relat_1(k7_relat_1(sK0,X22),k1_relat_1(k7_relat_1(sK0,X22))) = k2_relat_1(k7_relat_1(sK0,X22))) )),
% 18.45/2.68    inference(resolution,[],[f64,f44])).
% 18.45/2.68  fof(f64,plain,(
% 18.45/2.68    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k7_relat_1(X2,X3),k1_relat_1(k7_relat_1(X2,X3))) = k2_relat_1(k7_relat_1(X2,X3))) )),
% 18.45/2.68    inference(resolution,[],[f48,f51])).
% 18.45/2.68  fof(f48,plain,(
% 18.45/2.68    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f20])).
% 18.45/2.68  fof(f20,plain,(
% 18.45/2.68    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 18.45/2.68    inference(ennf_transformation,[],[f6])).
% 18.45/2.68  fof(f6,axiom,(
% 18.45/2.68    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 18.45/2.68  fof(f13615,plain,(
% 18.45/2.68    r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK2),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 18.45/2.68    inference(superposition,[],[f830,f1665])).
% 18.45/2.68  fof(f1665,plain,(
% 18.45/2.68    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 18.45/2.68    inference(subsumption_resolution,[],[f1664,f44])).
% 18.45/2.68  fof(f1664,plain,(
% 18.45/2.68    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK0)),
% 18.45/2.68    inference(subsumption_resolution,[],[f1663,f42])).
% 18.45/2.68  fof(f42,plain,(
% 18.45/2.68    v1_relat_1(sK1)),
% 18.45/2.68    inference(cnf_transformation,[],[f19])).
% 18.45/2.68  fof(f1663,plain,(
% 18.45/2.68    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 18.45/2.68    inference(resolution,[],[f1439,f60])).
% 18.45/2.68  fof(f60,plain,(
% 18.45/2.68    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f35])).
% 18.45/2.68  fof(f35,plain,(
% 18.45/2.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 18.45/2.68    inference(flattening,[],[f34])).
% 18.45/2.68  fof(f34,plain,(
% 18.45/2.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 18.45/2.68    inference(ennf_transformation,[],[f3])).
% 18.45/2.68  fof(f3,axiom,(
% 18.45/2.68    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 18.45/2.68  fof(f1439,plain,(
% 18.45/2.68    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 18.45/2.68    inference(forward_demodulation,[],[f1434,f528])).
% 18.45/2.68  fof(f528,plain,(
% 18.45/2.68    ( ! [X15] : (k7_relat_1(k5_relat_1(sK0,sK1),X15) = k5_relat_1(k7_relat_1(sK0,X15),sK1)) )),
% 18.45/2.68    inference(resolution,[],[f457,f44])).
% 18.45/2.68  fof(f457,plain,(
% 18.45/2.68    ( ! [X14,X13] : (~v1_relat_1(X13) | k7_relat_1(k5_relat_1(X13,sK1),X14) = k5_relat_1(k7_relat_1(X13,X14),sK1)) )),
% 18.45/2.68    inference(resolution,[],[f55,f42])).
% 18.45/2.68  fof(f55,plain,(
% 18.45/2.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f28])).
% 18.45/2.68  fof(f28,plain,(
% 18.45/2.68    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 18.45/2.68    inference(ennf_transformation,[],[f5])).
% 18.45/2.68  fof(f5,axiom,(
% 18.45/2.68    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 18.45/2.68  fof(f1434,plain,(
% 18.45/2.68    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 18.45/2.68    inference(resolution,[],[f1360,f54])).
% 18.45/2.68  fof(f1360,plain,(
% 18.45/2.68    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(duplicate_literal_removal,[],[f1359])).
% 18.45/2.68  fof(f1359,plain,(
% 18.45/2.68    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(forward_demodulation,[],[f1358,f162])).
% 18.45/2.68  fof(f162,plain,(
% 18.45/2.68    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 18.45/2.68    inference(resolution,[],[f134,f44])).
% 18.45/2.68  fof(f134,plain,(
% 18.45/2.68    ( ! [X9] : (~v1_relat_1(X9) | k1_relat_1(k5_relat_1(X9,sK1)) = k10_relat_1(X9,k1_relat_1(sK1))) )),
% 18.45/2.68    inference(resolution,[],[f50,f42])).
% 18.45/2.68  fof(f50,plain,(
% 18.45/2.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 18.45/2.68    inference(cnf_transformation,[],[f22])).
% 18.45/2.68  fof(f22,plain,(
% 18.45/2.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 18.45/2.68    inference(ennf_transformation,[],[f8])).
% 18.45/2.68  fof(f8,axiom,(
% 18.45/2.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 18.45/2.68  fof(f1358,plain,(
% 18.45/2.68    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(subsumption_resolution,[],[f1357,f40])).
% 18.45/2.68  fof(f40,plain,(
% 18.45/2.68    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(sK0))),
% 18.45/2.68    inference(cnf_transformation,[],[f19])).
% 18.45/2.68  fof(f1357,plain,(
% 18.45/2.68    ~r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(subsumption_resolution,[],[f1356,f44])).
% 18.45/2.68  fof(f1356,plain,(
% 18.45/2.68    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(subsumption_resolution,[],[f1306,f45])).
% 18.45/2.68  fof(f45,plain,(
% 18.45/2.68    v1_funct_1(sK0)),
% 18.45/2.68    inference(cnf_transformation,[],[f19])).
% 18.45/2.68  fof(f1306,plain,(
% 18.45/2.68    ~v1_funct_1(sK0) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(resolution,[],[f62,f41])).
% 18.45/2.68  fof(f41,plain,(
% 18.45/2.68    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.68    inference(cnf_transformation,[],[f19])).
% 18.45/2.68  fof(f62,plain,(
% 18.45/2.68    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 18.45/2.68    inference(cnf_transformation,[],[f38])).
% 18.45/2.68  fof(f38,plain,(
% 18.45/2.68    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 18.45/2.68    inference(flattening,[],[f37])).
% 18.45/2.68  fof(f37,plain,(
% 18.45/2.68    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 18.45/2.68    inference(ennf_transformation,[],[f15])).
% 18.45/2.68  fof(f15,axiom,(
% 18.45/2.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 18.45/2.68  fof(f830,plain,(
% 18.45/2.68    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK0,X0))) )),
% 18.45/2.68    inference(subsumption_resolution,[],[f829,f115])).
% 18.45/2.68  fof(f115,plain,(
% 18.45/2.68    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0))) )),
% 18.45/2.68    inference(subsumption_resolution,[],[f114,f46])).
% 18.45/2.68  fof(f46,plain,(
% 18.45/2.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 18.45/2.68    inference(cnf_transformation,[],[f13])).
% 18.45/2.68  fof(f13,axiom,(
% 18.45/2.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 18.45/2.68  fof(f114,plain,(
% 18.45/2.68    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 18.45/2.68    inference(subsumption_resolution,[],[f113,f45])).
% 18.45/2.68  fof(f113,plain,(
% 18.45/2.68    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 18.45/2.68    inference(subsumption_resolution,[],[f112,f44])).
% 18.45/2.68  fof(f112,plain,(
% 18.45/2.68    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 18.45/2.68    inference(subsumption_resolution,[],[f109,f47])).
% 18.45/2.68  fof(f47,plain,(
% 18.45/2.68    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 18.45/2.68    inference(cnf_transformation,[],[f13])).
% 18.45/2.68  fof(f109,plain,(
% 18.45/2.68    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 18.45/2.68    inference(superposition,[],[f58,f72])).
% 18.45/2.68  fof(f72,plain,(
% 18.45/2.68    ( ! [X8] : (k7_relat_1(sK0,X8) = k5_relat_1(k6_relat_1(X8),sK0)) )),
% 18.45/2.68    inference(resolution,[],[f52,f44])).
% 18.45/2.68  fof(f52,plain,(
% 18.45/2.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f24])).
% 18.45/2.68  fof(f24,plain,(
% 18.45/2.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 18.45/2.68    inference(ennf_transformation,[],[f11])).
% 18.45/2.68  fof(f11,axiom,(
% 18.45/2.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 18.45/2.68  fof(f58,plain,(
% 18.45/2.68    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f31])).
% 18.45/2.68  fof(f31,plain,(
% 18.45/2.68    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 18.45/2.68    inference(flattening,[],[f30])).
% 18.45/2.68  fof(f30,plain,(
% 18.45/2.68    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 18.45/2.68    inference(ennf_transformation,[],[f12])).
% 18.45/2.68  fof(f12,axiom,(
% 18.45/2.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 18.45/2.68  fof(f829,plain,(
% 18.45/2.68    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1)) | ~v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(k7_relat_1(sK0,X0))) )),
% 18.45/2.68    inference(superposition,[],[f59,f826])).
% 18.45/2.68  fof(f826,plain,(
% 18.45/2.68    ( ! [X32] : (k1_relat_1(k5_relat_1(k7_relat_1(sK0,X32),sK1)) = k10_relat_1(k7_relat_1(sK0,X32),k1_relat_1(sK1))) )),
% 18.45/2.68    inference(resolution,[],[f160,f44])).
% 18.45/2.68  fof(f160,plain,(
% 18.45/2.68    ( ! [X2,X3] : (~v1_relat_1(X2) | k1_relat_1(k5_relat_1(k7_relat_1(X2,X3),sK1)) = k10_relat_1(k7_relat_1(X2,X3),k1_relat_1(sK1))) )),
% 18.45/2.68    inference(resolution,[],[f134,f51])).
% 18.45/2.68  fof(f59,plain,(
% 18.45/2.68    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 18.45/2.68    inference(cnf_transformation,[],[f33])).
% 18.45/2.68  fof(f33,plain,(
% 18.45/2.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 18.45/2.68    inference(flattening,[],[f32])).
% 18.45/2.68  fof(f32,plain,(
% 18.45/2.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 18.45/2.68    inference(ennf_transformation,[],[f14])).
% 18.45/2.68  fof(f14,axiom,(
% 18.45/2.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 18.45/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 18.45/2.69  fof(f1485,plain,(
% 18.45/2.69    r1_tarski(sK2,k1_relat_1(sK0))),
% 18.45/2.69    inference(subsumption_resolution,[],[f1484,f44])).
% 18.45/2.69  fof(f1484,plain,(
% 18.45/2.69    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 18.45/2.69    inference(subsumption_resolution,[],[f1481,f42])).
% 18.45/2.69  fof(f1481,plain,(
% 18.45/2.69    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 18.45/2.69    inference(resolution,[],[f1479,f49])).
% 18.45/2.69  fof(f49,plain,(
% 18.45/2.69    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 18.45/2.69    inference(cnf_transformation,[],[f21])).
% 18.45/2.69  fof(f21,plain,(
% 18.45/2.69    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 18.45/2.69    inference(ennf_transformation,[],[f9])).
% 18.45/2.69  fof(f9,axiom,(
% 18.45/2.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 18.45/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 18.45/2.69  fof(f1479,plain,(
% 18.45/2.69    ( ! [X0] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) | r1_tarski(sK2,X0)) )),
% 18.45/2.69    inference(superposition,[],[f61,f1438])).
% 18.45/2.69  fof(f1438,plain,(
% 18.45/2.69    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 18.45/2.69    inference(resolution,[],[f1360,f56])).
% 18.45/2.69  fof(f56,plain,(
% 18.45/2.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 18.45/2.69    inference(cnf_transformation,[],[f29])).
% 18.45/2.69  fof(f29,plain,(
% 18.45/2.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 18.45/2.69    inference(ennf_transformation,[],[f2])).
% 18.45/2.69  fof(f2,axiom,(
% 18.45/2.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 18.45/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 18.45/2.69  fof(f61,plain,(
% 18.45/2.69    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 18.45/2.69    inference(cnf_transformation,[],[f36])).
% 18.45/2.69  fof(f36,plain,(
% 18.45/2.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 18.45/2.69    inference(ennf_transformation,[],[f1])).
% 18.45/2.69  fof(f1,axiom,(
% 18.45/2.69    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 18.45/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 18.45/2.69  fof(f1433,plain,(
% 18.45/2.69    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 18.45/2.69    inference(resolution,[],[f1360,f39])).
% 18.45/2.69  fof(f39,plain,(
% 18.45/2.69    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 18.45/2.69    inference(cnf_transformation,[],[f19])).
% 18.45/2.69  % SZS output end Proof for theBenchmark
% 18.45/2.69  % (21572)------------------------------
% 18.45/2.69  % (21572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.45/2.69  % (21572)Termination reason: Refutation
% 18.45/2.69  
% 18.45/2.69  % (21572)Memory used [KB]: 36843
% 18.45/2.69  % (21572)Time elapsed: 2.282 s
% 18.45/2.69  % (21572)------------------------------
% 18.45/2.69  % (21572)------------------------------
% 18.45/2.69  % (21557)Success in time 2.331 s
%------------------------------------------------------------------------------
