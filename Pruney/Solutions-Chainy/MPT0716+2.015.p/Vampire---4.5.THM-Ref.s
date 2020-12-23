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

% Result     : Theorem 3.75s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 613 expanded)
%              Number of leaves         :   16 ( 125 expanded)
%              Depth                    :   20
%              Number of atoms          :  282 (2427 expanded)
%              Number of equality atoms :   49 ( 175 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4538,plain,(
    $false ),
    inference(global_subsumption,[],[f3416,f3551,f4537])).

fof(f4537,plain,(
    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f4533,f3569])).

fof(f3569,plain,(
    k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f718,f3557])).

fof(f3557,plain,(
    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f3552,f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(f3552,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f3551,f54])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f718,plain,(
    ! [X0] : k9_relat_1(sK0,X0) = k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f716,f82])).

fof(f82,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f716,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(superposition,[],[f688,f545])).

fof(f545,plain,(
    ! [X8] : k7_relat_1(sK0,X8) = k7_relat_1(k7_relat_1(sK0,X8),k1_relat_1(k7_relat_1(sK0,X8))) ),
    inference(resolution,[],[f63,f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f48,f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f688,plain,(
    ! [X6,X5] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X6)) = k9_relat_1(k7_relat_1(sK0,X5),X6) ),
    inference(resolution,[],[f684,f53])).

fof(f684,plain,(
    ! [X1] : v1_relat_1(k7_relat_1(sK0,X1)) ),
    inference(subsumption_resolution,[],[f683,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f683,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | v1_relat_1(k7_relat_1(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f682,f64])).

fof(f64,plain,(
    ! [X2] : k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X2))) ),
    inference(resolution,[],[f48,f46])).

fof(f682,plain,(
    ! [X1] :
      ( v1_relat_1(k7_relat_1(sK0,X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) ) ),
    inference(superposition,[],[f624,f619])).

fof(f619,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f615,f75])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f615,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[],[f588,f64])).

fof(f588,plain,(
    ! [X6,X7] : k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),sK0) = k7_relat_1(k7_relat_1(sK0,X6),X7) ),
    inference(forward_demodulation,[],[f585,f75])).

fof(f585,plain,(
    ! [X6,X7] : k7_relat_1(k5_relat_1(k6_relat_1(X6),sK0),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),sK0) ),
    inference(resolution,[],[f570,f46])).

fof(f570,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(X11)
      | k7_relat_1(k5_relat_1(X11,sK0),X12) = k5_relat_1(k7_relat_1(X11,X12),sK0) ) ),
    inference(resolution,[],[f55,f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f624,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(sK0,X4),X5))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) ) ),
    inference(subsumption_resolution,[],[f618,f44])).

fof(f618,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(sK0,X4),X5))
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) ) ),
    inference(superposition,[],[f60,f588])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f4533,plain,(
    r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK2),k1_relat_1(sK1)) ),
    inference(superposition,[],[f969,f4531])).

fof(f4531,plain,(
    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(subsumption_resolution,[],[f4530,f44])).

fof(f4530,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f4529,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f4529,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f3422,f60])).

fof(f3422,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f3417,f761])).

fof(f761,plain,(
    ! [X17] : k7_relat_1(k5_relat_1(sK0,sK1),X17) = k5_relat_1(k7_relat_1(sK0,X17),sK1) ),
    inference(resolution,[],[f571,f44])).

fof(f571,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(X13)
      | k7_relat_1(k5_relat_1(X13,sK1),X14) = k5_relat_1(k7_relat_1(X13,X14),sK1) ) ),
    inference(resolution,[],[f55,f42])).

fof(f3417,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f3321,f54])).

fof(f3321,plain,(
    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f3320])).

fof(f3320,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3319,f213])).

fof(f213,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f181,f44])).

fof(f181,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f3319,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3318,f40])).

fof(f40,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3318,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3317,f44])).

fof(f3317,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f3101,f45])).

fof(f45,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3101,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f969,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f968,f684])).

fof(f968,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1))
      | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f967,f139])).

fof(f139,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK0,X0)) ),
    inference(subsumption_resolution,[],[f138,f46])).

fof(f138,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f44])).

fof(f136,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f47,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f133,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f58,f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f967,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1))
      | ~ v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(superposition,[],[f59,f694])).

fof(f694,plain,(
    ! [X18] : k1_relat_1(k5_relat_1(k7_relat_1(sK0,X18),sK1)) = k10_relat_1(k7_relat_1(sK0,X18),k1_relat_1(sK1)) ),
    inference(resolution,[],[f684,f181])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f3551,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f3550,f44])).

fof(f3550,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f3546,f42])).

fof(f3546,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f3544,f49])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f3544,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f61,f3421])).

fof(f3421,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f3321,f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f3416,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f3321,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:33:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (16865)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (16871)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (16885)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.49  % (16867)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (16873)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (16882)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (16869)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (16876)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (16889)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (16870)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (16874)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (16881)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (16878)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (16866)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (16889)Refutation not found, incomplete strategy% (16889)------------------------------
% 0.21/0.51  % (16889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16889)Memory used [KB]: 10618
% 0.21/0.51  % (16889)Time elapsed: 0.055 s
% 0.21/0.51  % (16889)------------------------------
% 0.21/0.51  % (16889)------------------------------
% 0.21/0.51  % (16883)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (16872)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16879)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (16887)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (16888)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.25/0.52  % (16880)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.25/0.52  % (16875)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.25/0.52  % (16868)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.25/0.52  % (16868)Refutation not found, incomplete strategy% (16868)------------------------------
% 1.25/0.52  % (16868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (16868)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (16868)Memory used [KB]: 10618
% 1.25/0.52  % (16868)Time elapsed: 0.104 s
% 1.25/0.52  % (16868)------------------------------
% 1.25/0.52  % (16868)------------------------------
% 1.25/0.52  % (16875)Refutation not found, incomplete strategy% (16875)------------------------------
% 1.25/0.52  % (16875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (16875)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (16875)Memory used [KB]: 10618
% 1.25/0.52  % (16875)Time elapsed: 0.109 s
% 1.25/0.52  % (16875)------------------------------
% 1.25/0.52  % (16875)------------------------------
% 1.25/0.53  % (16884)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.25/0.53  % (16886)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.38/0.59  % (16888)Refutation not found, incomplete strategy% (16888)------------------------------
% 1.38/0.59  % (16888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.59  % (16888)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.59  
% 1.38/0.59  % (16888)Memory used [KB]: 1663
% 1.38/0.59  % (16888)Time elapsed: 0.169 s
% 1.38/0.59  % (16888)------------------------------
% 1.38/0.59  % (16888)------------------------------
% 3.75/0.88  % (16879)Refutation found. Thanks to Tanya!
% 3.75/0.88  % SZS status Theorem for theBenchmark
% 3.75/0.88  % SZS output start Proof for theBenchmark
% 3.75/0.89  fof(f4538,plain,(
% 3.75/0.89    $false),
% 3.75/0.89    inference(global_subsumption,[],[f3416,f3551,f4537])).
% 3.75/0.89  fof(f4537,plain,(
% 3.75/0.89    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 3.75/0.89    inference(forward_demodulation,[],[f4533,f3569])).
% 3.75/0.89  fof(f3569,plain,(
% 3.75/0.89    k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK2),sK2)),
% 3.75/0.89    inference(superposition,[],[f718,f3557])).
% 3.75/0.89  fof(f3557,plain,(
% 3.75/0.89    sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 3.75/0.89    inference(subsumption_resolution,[],[f3552,f44])).
% 3.75/0.89  fof(f44,plain,(
% 3.75/0.89    v1_relat_1(sK0)),
% 3.75/0.89    inference(cnf_transformation,[],[f19])).
% 3.75/0.89  fof(f19,plain,(
% 3.75/0.89    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.75/0.89    inference(flattening,[],[f18])).
% 3.75/0.89  fof(f18,plain,(
% 3.75/0.89    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.75/0.89    inference(ennf_transformation,[],[f17])).
% 3.75/0.89  fof(f17,negated_conjecture,(
% 3.75/0.89    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.75/0.89    inference(negated_conjecture,[],[f16])).
% 3.75/0.89  fof(f16,conjecture,(
% 3.75/0.89    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).
% 3.75/0.89  fof(f3552,plain,(
% 3.75/0.89    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 3.75/0.89    inference(resolution,[],[f3551,f54])).
% 3.75/0.89  fof(f54,plain,(
% 3.75/0.89    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 3.75/0.89    inference(cnf_transformation,[],[f27])).
% 3.75/0.89  fof(f27,plain,(
% 3.75/0.89    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.75/0.89    inference(flattening,[],[f26])).
% 3.75/0.89  fof(f26,plain,(
% 3.75/0.89    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.75/0.89    inference(ennf_transformation,[],[f9])).
% 3.75/0.89  fof(f9,axiom,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 3.75/0.89  fof(f718,plain,(
% 3.75/0.89    ( ! [X0] : (k9_relat_1(sK0,X0) = k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 3.75/0.89    inference(forward_demodulation,[],[f716,f82])).
% 3.75/0.89  fof(f82,plain,(
% 3.75/0.89    ( ! [X8] : (k2_relat_1(k7_relat_1(sK0,X8)) = k9_relat_1(sK0,X8)) )),
% 3.75/0.89    inference(resolution,[],[f53,f44])).
% 3.75/0.89  fof(f53,plain,(
% 3.75/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f25])).
% 3.75/0.89  fof(f25,plain,(
% 3.75/0.89    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.75/0.89    inference(ennf_transformation,[],[f6])).
% 3.75/0.89  fof(f6,axiom,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.75/0.89  fof(f716,plain,(
% 3.75/0.89    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 3.75/0.89    inference(superposition,[],[f688,f545])).
% 3.75/0.89  fof(f545,plain,(
% 3.75/0.89    ( ! [X8] : (k7_relat_1(sK0,X8) = k7_relat_1(k7_relat_1(sK0,X8),k1_relat_1(k7_relat_1(sK0,X8)))) )),
% 3.75/0.89    inference(resolution,[],[f63,f44])).
% 3.75/0.89  fof(f63,plain,(
% 3.75/0.89    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1)))) )),
% 3.75/0.89    inference(resolution,[],[f48,f51])).
% 3.75/0.89  fof(f51,plain,(
% 3.75/0.89    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f23])).
% 3.75/0.89  fof(f23,plain,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.75/0.89    inference(ennf_transformation,[],[f4])).
% 3.75/0.89  fof(f4,axiom,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.75/0.89  fof(f48,plain,(
% 3.75/0.89    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 3.75/0.89    inference(cnf_transformation,[],[f20])).
% 3.75/0.89  fof(f20,plain,(
% 3.75/0.89    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.75/0.89    inference(ennf_transformation,[],[f11])).
% 3.75/0.89  fof(f11,axiom,(
% 3.75/0.89    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 3.75/0.89  fof(f688,plain,(
% 3.75/0.89    ( ! [X6,X5] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X6)) = k9_relat_1(k7_relat_1(sK0,X5),X6)) )),
% 3.75/0.89    inference(resolution,[],[f684,f53])).
% 3.75/0.89  fof(f684,plain,(
% 3.75/0.89    ( ! [X1] : (v1_relat_1(k7_relat_1(sK0,X1))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f683,f46])).
% 3.75/0.89  fof(f46,plain,(
% 3.75/0.89    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.75/0.89    inference(cnf_transformation,[],[f13])).
% 3.75/0.89  fof(f13,axiom,(
% 3.75/0.89    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.75/0.89  fof(f683,plain,(
% 3.75/0.89    ( ! [X1] : (~v1_relat_1(k6_relat_1(X1)) | v1_relat_1(k7_relat_1(sK0,X1))) )),
% 3.75/0.89    inference(forward_demodulation,[],[f682,f64])).
% 3.75/0.89  fof(f64,plain,(
% 3.75/0.89    ( ! [X2] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X2)))) )),
% 3.75/0.89    inference(resolution,[],[f48,f46])).
% 3.75/0.89  fof(f682,plain,(
% 3.75/0.89    ( ! [X1] : (v1_relat_1(k7_relat_1(sK0,X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) )),
% 3.75/0.89    inference(superposition,[],[f624,f619])).
% 3.75/0.89  fof(f619,plain,(
% 3.75/0.89    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k6_relat_1(X0)))) )),
% 3.75/0.89    inference(forward_demodulation,[],[f615,f75])).
% 3.75/0.89  fof(f75,plain,(
% 3.75/0.89    ( ! [X8] : (k7_relat_1(sK0,X8) = k5_relat_1(k6_relat_1(X8),sK0)) )),
% 3.75/0.89    inference(resolution,[],[f52,f44])).
% 3.75/0.89  fof(f52,plain,(
% 3.75/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f24])).
% 3.75/0.89  fof(f24,plain,(
% 3.75/0.89    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.75/0.89    inference(ennf_transformation,[],[f10])).
% 3.75/0.89  fof(f10,axiom,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 3.75/0.89  fof(f615,plain,(
% 3.75/0.89    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k6_relat_1(X0)))) )),
% 3.75/0.89    inference(superposition,[],[f588,f64])).
% 3.75/0.89  fof(f588,plain,(
% 3.75/0.89    ( ! [X6,X7] : (k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),sK0) = k7_relat_1(k7_relat_1(sK0,X6),X7)) )),
% 3.75/0.89    inference(forward_demodulation,[],[f585,f75])).
% 3.75/0.89  fof(f585,plain,(
% 3.75/0.89    ( ! [X6,X7] : (k7_relat_1(k5_relat_1(k6_relat_1(X6),sK0),X7) = k5_relat_1(k7_relat_1(k6_relat_1(X6),X7),sK0)) )),
% 3.75/0.89    inference(resolution,[],[f570,f46])).
% 3.75/0.89  fof(f570,plain,(
% 3.75/0.89    ( ! [X12,X11] : (~v1_relat_1(X11) | k7_relat_1(k5_relat_1(X11,sK0),X12) = k5_relat_1(k7_relat_1(X11,X12),sK0)) )),
% 3.75/0.89    inference(resolution,[],[f55,f44])).
% 3.75/0.89  fof(f55,plain,(
% 3.75/0.89    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f28])).
% 3.75/0.89  fof(f28,plain,(
% 3.75/0.89    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.75/0.89    inference(ennf_transformation,[],[f5])).
% 3.75/0.89  fof(f5,axiom,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 3.75/0.89  fof(f624,plain,(
% 3.75/0.89    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(k7_relat_1(sK0,X4),X5)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f618,f44])).
% 3.75/0.89  fof(f618,plain,(
% 3.75/0.89    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(k7_relat_1(sK0,X4),X5)) | ~v1_relat_1(sK0) | ~v1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) )),
% 3.75/0.89    inference(superposition,[],[f60,f588])).
% 3.75/0.89  fof(f60,plain,(
% 3.75/0.89    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f35])).
% 3.75/0.89  fof(f35,plain,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.75/0.89    inference(flattening,[],[f34])).
% 3.75/0.89  fof(f34,plain,(
% 3.75/0.89    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.75/0.89    inference(ennf_transformation,[],[f3])).
% 3.75/0.89  fof(f3,axiom,(
% 3.75/0.89    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 3.75/0.89  fof(f4533,plain,(
% 3.75/0.89    r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK2),k1_relat_1(sK1))),
% 3.75/0.89    inference(superposition,[],[f969,f4531])).
% 3.75/0.89  fof(f4531,plain,(
% 3.75/0.89    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 3.75/0.89    inference(subsumption_resolution,[],[f4530,f44])).
% 3.75/0.89  fof(f4530,plain,(
% 3.75/0.89    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK0)),
% 3.75/0.89    inference(subsumption_resolution,[],[f4529,f42])).
% 3.75/0.89  fof(f42,plain,(
% 3.75/0.89    v1_relat_1(sK1)),
% 3.75/0.89    inference(cnf_transformation,[],[f19])).
% 3.75/0.89  fof(f4529,plain,(
% 3.75/0.89    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.75/0.89    inference(resolution,[],[f3422,f60])).
% 3.75/0.89  fof(f3422,plain,(
% 3.75/0.89    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 3.75/0.89    inference(forward_demodulation,[],[f3417,f761])).
% 3.75/0.89  fof(f761,plain,(
% 3.75/0.89    ( ! [X17] : (k7_relat_1(k5_relat_1(sK0,sK1),X17) = k5_relat_1(k7_relat_1(sK0,X17),sK1)) )),
% 3.75/0.89    inference(resolution,[],[f571,f44])).
% 3.75/0.89  fof(f571,plain,(
% 3.75/0.89    ( ! [X14,X13] : (~v1_relat_1(X13) | k7_relat_1(k5_relat_1(X13,sK1),X14) = k5_relat_1(k7_relat_1(X13,X14),sK1)) )),
% 3.75/0.89    inference(resolution,[],[f55,f42])).
% 3.75/0.89  fof(f3417,plain,(
% 3.75/0.89    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 3.75/0.89    inference(resolution,[],[f3321,f54])).
% 3.75/0.89  fof(f3321,plain,(
% 3.75/0.89    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(duplicate_literal_removal,[],[f3320])).
% 3.75/0.89  fof(f3320,plain,(
% 3.75/0.89    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(forward_demodulation,[],[f3319,f213])).
% 3.75/0.89  fof(f213,plain,(
% 3.75/0.89    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 3.75/0.89    inference(resolution,[],[f181,f44])).
% 3.75/0.89  fof(f181,plain,(
% 3.75/0.89    ( ! [X9] : (~v1_relat_1(X9) | k1_relat_1(k5_relat_1(X9,sK1)) = k10_relat_1(X9,k1_relat_1(sK1))) )),
% 3.75/0.89    inference(resolution,[],[f50,f42])).
% 3.75/0.89  fof(f50,plain,(
% 3.75/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 3.75/0.89    inference(cnf_transformation,[],[f22])).
% 3.75/0.89  fof(f22,plain,(
% 3.75/0.89    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.89    inference(ennf_transformation,[],[f7])).
% 3.75/0.89  fof(f7,axiom,(
% 3.75/0.89    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 3.75/0.89  fof(f3319,plain,(
% 3.75/0.89    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(subsumption_resolution,[],[f3318,f40])).
% 3.75/0.89  fof(f40,plain,(
% 3.75/0.89    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(sK0))),
% 3.75/0.89    inference(cnf_transformation,[],[f19])).
% 3.75/0.89  fof(f3318,plain,(
% 3.75/0.89    ~r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(subsumption_resolution,[],[f3317,f44])).
% 3.75/0.89  fof(f3317,plain,(
% 3.75/0.89    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(subsumption_resolution,[],[f3101,f45])).
% 3.75/0.89  fof(f45,plain,(
% 3.75/0.89    v1_funct_1(sK0)),
% 3.75/0.89    inference(cnf_transformation,[],[f19])).
% 3.75/0.89  fof(f3101,plain,(
% 3.75/0.89    ~v1_funct_1(sK0) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(resolution,[],[f62,f41])).
% 3.75/0.89  fof(f41,plain,(
% 3.75/0.89    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(cnf_transformation,[],[f19])).
% 3.75/0.89  fof(f62,plain,(
% 3.75/0.89    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 3.75/0.89    inference(cnf_transformation,[],[f38])).
% 3.75/0.89  fof(f38,plain,(
% 3.75/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.75/0.89    inference(flattening,[],[f37])).
% 3.75/0.89  fof(f37,plain,(
% 3.75/0.89    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.75/0.89    inference(ennf_transformation,[],[f15])).
% 3.75/0.89  fof(f15,axiom,(
% 3.75/0.89    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 3.75/0.89  fof(f969,plain,(
% 3.75/0.89    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f968,f684])).
% 3.75/0.89  fof(f968,plain,(
% 3.75/0.89    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK0,X0))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f967,f139])).
% 3.75/0.89  fof(f139,plain,(
% 3.75/0.89    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f138,f46])).
% 3.75/0.89  fof(f138,plain,(
% 3.75/0.89    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f137,f45])).
% 3.75/0.89  fof(f137,plain,(
% 3.75/0.89    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f136,f44])).
% 3.75/0.89  fof(f136,plain,(
% 3.75/0.89    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.75/0.89    inference(subsumption_resolution,[],[f133,f47])).
% 3.75/0.89  fof(f47,plain,(
% 3.75/0.89    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.75/0.89    inference(cnf_transformation,[],[f13])).
% 3.75/0.89  fof(f133,plain,(
% 3.75/0.89    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.75/0.89    inference(superposition,[],[f58,f75])).
% 3.75/0.89  fof(f58,plain,(
% 3.75/0.89    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f31])).
% 3.75/0.89  fof(f31,plain,(
% 3.75/0.89    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.75/0.89    inference(flattening,[],[f30])).
% 3.75/0.89  fof(f30,plain,(
% 3.75/0.89    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.75/0.89    inference(ennf_transformation,[],[f12])).
% 3.75/0.89  fof(f12,axiom,(
% 3.75/0.89    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 3.75/0.89  fof(f967,plain,(
% 3.75/0.89    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X0),k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))),k1_relat_1(sK1)) | ~v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(k7_relat_1(sK0,X0))) )),
% 3.75/0.89    inference(superposition,[],[f59,f694])).
% 3.75/0.89  fof(f694,plain,(
% 3.75/0.89    ( ! [X18] : (k1_relat_1(k5_relat_1(k7_relat_1(sK0,X18),sK1)) = k10_relat_1(k7_relat_1(sK0,X18),k1_relat_1(sK1))) )),
% 3.75/0.89    inference(resolution,[],[f684,f181])).
% 3.75/0.89  fof(f59,plain,(
% 3.75/0.89    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f33])).
% 3.75/0.89  fof(f33,plain,(
% 3.75/0.89    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.75/0.89    inference(flattening,[],[f32])).
% 3.75/0.89  fof(f32,plain,(
% 3.75/0.89    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.75/0.89    inference(ennf_transformation,[],[f14])).
% 3.75/0.89  fof(f14,axiom,(
% 3.75/0.89    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 3.75/0.89  fof(f3551,plain,(
% 3.75/0.89    r1_tarski(sK2,k1_relat_1(sK0))),
% 3.75/0.89    inference(subsumption_resolution,[],[f3550,f44])).
% 3.75/0.89  fof(f3550,plain,(
% 3.75/0.89    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 3.75/0.89    inference(subsumption_resolution,[],[f3546,f42])).
% 3.75/0.89  fof(f3546,plain,(
% 3.75/0.89    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 3.75/0.89    inference(resolution,[],[f3544,f49])).
% 3.75/0.89  fof(f49,plain,(
% 3.75/0.89    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f21])).
% 3.75/0.89  fof(f21,plain,(
% 3.75/0.89    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.89    inference(ennf_transformation,[],[f8])).
% 3.75/0.89  fof(f8,axiom,(
% 3.75/0.89    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 3.75/0.89  fof(f3544,plain,(
% 3.75/0.89    ( ! [X0] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) | r1_tarski(sK2,X0)) )),
% 3.75/0.89    inference(superposition,[],[f61,f3421])).
% 3.75/0.89  fof(f3421,plain,(
% 3.75/0.89    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 3.75/0.89    inference(resolution,[],[f3321,f56])).
% 3.75/0.89  fof(f56,plain,(
% 3.75/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.75/0.89    inference(cnf_transformation,[],[f29])).
% 3.75/0.89  fof(f29,plain,(
% 3.75/0.89    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.75/0.89    inference(ennf_transformation,[],[f2])).
% 3.75/0.89  fof(f2,axiom,(
% 3.75/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.75/0.89  fof(f61,plain,(
% 3.75/0.89    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 3.75/0.89    inference(cnf_transformation,[],[f36])).
% 3.75/0.89  fof(f36,plain,(
% 3.75/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.75/0.89    inference(ennf_transformation,[],[f1])).
% 3.75/0.89  fof(f1,axiom,(
% 3.75/0.89    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.75/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 3.75/0.89  fof(f3416,plain,(
% 3.75/0.89    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 3.75/0.89    inference(resolution,[],[f3321,f39])).
% 3.75/0.89  fof(f39,plain,(
% 3.75/0.89    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 3.75/0.89    inference(cnf_transformation,[],[f19])).
% 3.75/0.89  % SZS output end Proof for theBenchmark
% 3.75/0.89  % (16879)------------------------------
% 3.75/0.89  % (16879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.89  % (16879)Termination reason: Refutation
% 3.75/0.89  
% 3.75/0.89  % (16879)Memory used [KB]: 13432
% 3.75/0.89  % (16879)Time elapsed: 0.477 s
% 3.75/0.89  % (16879)------------------------------
% 3.75/0.89  % (16879)------------------------------
% 3.75/0.89  % (16861)Success in time 0.525 s
%------------------------------------------------------------------------------
