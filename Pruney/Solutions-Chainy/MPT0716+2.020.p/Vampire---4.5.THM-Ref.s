%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 4.57s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 300 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   28
%              Number of atoms          :  258 (1379 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2129,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f2129,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f2128,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2128,plain,(
    ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f2127,f38])).

fof(f2127,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2126,f39])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f2126,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f2125,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f2125,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f2124,f552])).

fof(f552,plain,(
    ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f547,f91])).

fof(f91,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,
    ( ~ v1_relat_1(sK1)
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X2,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f547,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f546,f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f546,plain,(
    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f544,f74])).

fof(f74,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f67,f38])).

fof(f67,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(X7,sK1)) = k10_relat_1(X7,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f544,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f543,f38])).

fof(f543,plain,
    ( ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f542,f91])).

fof(f542,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f539,f39])).

fof(f539,plain,
    ( ~ v1_funct_1(sK0)
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f2124,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2123,f55])).

fof(f55,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2123,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2122,f36])).

fof(f2122,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2121,f37])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f2121,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2076,f94])).

fof(f94,plain,(
    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f92,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2076,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(superposition,[],[f42,f562])).

fof(f562,plain,(
    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(subsumption_resolution,[],[f561,f38])).

fof(f561,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f560,f36])).

fof(f560,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f553,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f553,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f549,f137])).

fof(f137,plain,(
    ! [X10] : k7_relat_1(k5_relat_1(sK0,sK1),X10) = k5_relat_1(k7_relat_1(sK0,X10),sK1) ),
    inference(resolution,[],[f110,f38])).

fof(f110,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1) ) ),
    inference(resolution,[],[f46,f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f549,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f546,f45])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:09:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (25369)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.43  % (25383)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.44  % (25384)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.50  % (25377)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.50  % (25363)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (25367)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (25366)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (25372)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (25382)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (25380)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (25371)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (25364)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (25374)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.54  % (25379)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.54  % (25378)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (25381)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.54  % (25365)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.54  % (25373)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.55  % (25370)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.55  % (25375)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.55  % (25387)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.55  % (25385)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.55  % (25388)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.56  % (25376)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 4.41/0.93  % (25371)Time limit reached!
% 4.41/0.93  % (25371)------------------------------
% 4.41/0.93  % (25371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.93  % (25371)Termination reason: Time limit
% 4.41/0.93  
% 4.41/0.93  % (25371)Memory used [KB]: 13688
% 4.41/0.93  % (25371)Time elapsed: 0.514 s
% 4.41/0.93  % (25371)------------------------------
% 4.41/0.93  % (25371)------------------------------
% 4.41/0.93  % (25376)Time limit reached!
% 4.41/0.93  % (25376)------------------------------
% 4.41/0.93  % (25376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.93  % (25376)Termination reason: Time limit
% 4.41/0.93  % (25376)Termination phase: Saturation
% 4.41/0.93  
% 4.41/0.93  % (25376)Memory used [KB]: 14583
% 4.41/0.93  % (25376)Time elapsed: 0.521 s
% 4.41/0.93  % (25376)------------------------------
% 4.41/0.93  % (25376)------------------------------
% 4.57/0.96  % (25377)Refutation found. Thanks to Tanya!
% 4.57/0.96  % SZS status Theorem for theBenchmark
% 4.57/0.96  % SZS output start Proof for theBenchmark
% 4.57/0.96  fof(f2130,plain,(
% 4.57/0.96    $false),
% 4.57/0.96    inference(subsumption_resolution,[],[f2129,f38])).
% 4.57/0.96  fof(f38,plain,(
% 4.57/0.96    v1_relat_1(sK0)),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f15,plain,(
% 4.57/0.96    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 4.57/0.96    inference(flattening,[],[f14])).
% 4.57/0.96  fof(f14,plain,(
% 4.57/0.96    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f13])).
% 4.57/0.96  fof(f13,negated_conjecture,(
% 4.57/0.96    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 4.57/0.96    inference(negated_conjecture,[],[f12])).
% 4.57/0.96  fof(f12,conjecture,(
% 4.57/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 4.57/0.96  fof(f2129,plain,(
% 4.57/0.96    ~v1_relat_1(sK0)),
% 4.57/0.96    inference(resolution,[],[f2128,f43])).
% 4.57/0.96  fof(f43,plain,(
% 4.57/0.96    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f20])).
% 4.57/0.96  fof(f20,plain,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.57/0.96    inference(ennf_transformation,[],[f3])).
% 4.57/0.96  fof(f3,axiom,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.57/0.96  fof(f2128,plain,(
% 4.57/0.96    ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 4.57/0.96    inference(subsumption_resolution,[],[f2127,f38])).
% 4.57/0.96  fof(f2127,plain,(
% 4.57/0.96    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f2126,f39])).
% 4.57/0.96  fof(f39,plain,(
% 4.57/0.96    v1_funct_1(sK0)),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f2126,plain,(
% 4.57/0.96    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 4.57/0.96    inference(resolution,[],[f2125,f48])).
% 4.57/0.96  fof(f48,plain,(
% 4.57/0.96    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f26])).
% 4.57/0.96  fof(f26,plain,(
% 4.57/0.96    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.57/0.96    inference(flattening,[],[f25])).
% 4.57/0.96  fof(f25,plain,(
% 4.57/0.96    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f9])).
% 4.57/0.96  fof(f9,axiom,(
% 4.57/0.96    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 4.57/0.96  fof(f2125,plain,(
% 4.57/0.96    ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 4.57/0.96    inference(subsumption_resolution,[],[f2124,f552])).
% 4.57/0.96  fof(f552,plain,(
% 4.57/0.96    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 4.57/0.96    inference(subsumption_resolution,[],[f547,f91])).
% 4.57/0.96  fof(f91,plain,(
% 4.57/0.96    r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(subsumption_resolution,[],[f90,f36])).
% 4.57/0.96  fof(f36,plain,(
% 4.57/0.96    v1_relat_1(sK1)),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f90,plain,(
% 4.57/0.96    ~v1_relat_1(sK1) | r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(subsumption_resolution,[],[f85,f38])).
% 4.57/0.96  fof(f85,plain,(
% 4.57/0.96    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f84])).
% 4.57/0.96  fof(f84,plain,(
% 4.57/0.96    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(resolution,[],[f57,f34])).
% 4.57/0.96  fof(f34,plain,(
% 4.57/0.96    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f57,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r1_tarski(X2,k1_relat_1(X1))) )),
% 4.57/0.96    inference(resolution,[],[f40,f51])).
% 4.57/0.96  fof(f51,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f32])).
% 4.57/0.96  fof(f32,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.57/0.96    inference(flattening,[],[f31])).
% 4.57/0.96  fof(f31,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.57/0.96    inference(ennf_transformation,[],[f1])).
% 4.57/0.96  fof(f1,axiom,(
% 4.57/0.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.57/0.96  fof(f40,plain,(
% 4.57/0.96    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f16])).
% 4.57/0.96  fof(f16,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.57/0.96    inference(ennf_transformation,[],[f7])).
% 4.57/0.96  fof(f7,axiom,(
% 4.57/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 4.57/0.96  fof(f547,plain,(
% 4.57/0.96    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(resolution,[],[f546,f33])).
% 4.57/0.96  fof(f33,plain,(
% 4.57/0.96    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f546,plain,(
% 4.57/0.96    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f545])).
% 4.57/0.96  fof(f545,plain,(
% 4.57/0.96    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(forward_demodulation,[],[f544,f74])).
% 4.57/0.96  fof(f74,plain,(
% 4.57/0.96    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 4.57/0.96    inference(resolution,[],[f67,f38])).
% 4.57/0.96  fof(f67,plain,(
% 4.57/0.96    ( ! [X7] : (~v1_relat_1(X7) | k1_relat_1(k5_relat_1(X7,sK1)) = k10_relat_1(X7,k1_relat_1(sK1))) )),
% 4.57/0.96    inference(resolution,[],[f41,f36])).
% 4.57/0.96  fof(f41,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 4.57/0.96    inference(cnf_transformation,[],[f17])).
% 4.57/0.96  fof(f17,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.57/0.96    inference(ennf_transformation,[],[f6])).
% 4.57/0.96  fof(f6,axiom,(
% 4.57/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 4.57/0.96  fof(f544,plain,(
% 4.57/0.96    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(subsumption_resolution,[],[f543,f38])).
% 4.57/0.96  fof(f543,plain,(
% 4.57/0.96    ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(subsumption_resolution,[],[f542,f91])).
% 4.57/0.96  fof(f542,plain,(
% 4.57/0.96    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(subsumption_resolution,[],[f539,f39])).
% 4.57/0.96  fof(f539,plain,(
% 4.57/0.96    ~v1_funct_1(sK0) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(resolution,[],[f50,f35])).
% 4.57/0.96  fof(f35,plain,(
% 4.57/0.96    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f50,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 4.57/0.96    inference(cnf_transformation,[],[f30])).
% 4.57/0.96  fof(f30,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.57/0.96    inference(flattening,[],[f29])).
% 4.57/0.96  fof(f29,plain,(
% 4.57/0.96    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.57/0.96    inference(ennf_transformation,[],[f10])).
% 4.57/0.96  fof(f10,axiom,(
% 4.57/0.96    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 4.57/0.96  fof(f2124,plain,(
% 4.57/0.96    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2))),
% 4.57/0.96    inference(forward_demodulation,[],[f2123,f55])).
% 4.57/0.96  fof(f55,plain,(
% 4.57/0.96    ( ! [X6] : (k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6)) )),
% 4.57/0.96    inference(resolution,[],[f44,f38])).
% 4.57/0.96  fof(f44,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f21])).
% 4.57/0.96  fof(f21,plain,(
% 4.57/0.96    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.57/0.96    inference(ennf_transformation,[],[f5])).
% 4.57/0.96  fof(f5,axiom,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 4.57/0.96  fof(f2123,plain,(
% 4.57/0.96    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 4.57/0.96    inference(subsumption_resolution,[],[f2122,f36])).
% 4.57/0.96  fof(f2122,plain,(
% 4.57/0.96    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 4.57/0.96    inference(subsumption_resolution,[],[f2121,f37])).
% 4.57/0.96  fof(f37,plain,(
% 4.57/0.96    v1_funct_1(sK1)),
% 4.57/0.96    inference(cnf_transformation,[],[f15])).
% 4.57/0.96  fof(f2121,plain,(
% 4.57/0.96    ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 4.57/0.96    inference(subsumption_resolution,[],[f2076,f94])).
% 4.57/0.96  fof(f94,plain,(
% 4.57/0.96    sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 4.57/0.96    inference(subsumption_resolution,[],[f92,f38])).
% 4.57/0.96  fof(f92,plain,(
% 4.57/0.96    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 4.57/0.96    inference(resolution,[],[f91,f45])).
% 4.57/0.96  fof(f45,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 4.57/0.96    inference(cnf_transformation,[],[f23])).
% 4.57/0.96  fof(f23,plain,(
% 4.57/0.96    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.57/0.96    inference(flattening,[],[f22])).
% 4.57/0.96  fof(f22,plain,(
% 4.57/0.96    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.57/0.96    inference(ennf_transformation,[],[f8])).
% 4.57/0.96  fof(f8,axiom,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 4.57/0.96  fof(f2076,plain,(
% 4.57/0.96    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 4.57/0.96    inference(superposition,[],[f42,f562])).
% 4.57/0.96  fof(f562,plain,(
% 4.57/0.96    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 4.57/0.96    inference(subsumption_resolution,[],[f561,f38])).
% 4.57/0.96  fof(f561,plain,(
% 4.57/0.96    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f560,f36])).
% 4.57/0.96  fof(f560,plain,(
% 4.57/0.96    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 4.57/0.96    inference(resolution,[],[f553,f49])).
% 4.57/0.96  fof(f49,plain,(
% 4.57/0.96    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f28])).
% 4.57/0.96  fof(f28,plain,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.57/0.96    inference(flattening,[],[f27])).
% 4.57/0.96  fof(f27,plain,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f2])).
% 4.57/0.96  fof(f2,axiom,(
% 4.57/0.96    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 4.57/0.96  fof(f553,plain,(
% 4.57/0.96    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 4.57/0.96    inference(forward_demodulation,[],[f549,f137])).
% 4.57/0.96  fof(f137,plain,(
% 4.57/0.96    ( ! [X10] : (k7_relat_1(k5_relat_1(sK0,sK1),X10) = k5_relat_1(k7_relat_1(sK0,X10),sK1)) )),
% 4.57/0.96    inference(resolution,[],[f110,f38])).
% 4.57/0.96  fof(f110,plain,(
% 4.57/0.96    ( ! [X10,X11] : (~v1_relat_1(X10) | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1)) )),
% 4.57/0.96    inference(resolution,[],[f46,f36])).
% 4.57/0.96  fof(f46,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f24])).
% 4.57/0.96  fof(f24,plain,(
% 4.57/0.96    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.57/0.96    inference(ennf_transformation,[],[f4])).
% 4.57/0.96  fof(f4,axiom,(
% 4.57/0.96    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 4.57/0.96  fof(f549,plain,(
% 4.57/0.96    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 4.57/0.96    inference(resolution,[],[f546,f45])).
% 4.57/0.96  fof(f42,plain,(
% 4.57/0.96    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 4.57/0.96    inference(cnf_transformation,[],[f19])).
% 4.57/0.96  fof(f19,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.57/0.96    inference(flattening,[],[f18])).
% 4.57/0.96  fof(f18,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f11])).
% 4.57/0.96  fof(f11,axiom,(
% 4.57/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 4.57/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 4.57/0.96  % SZS output end Proof for theBenchmark
% 4.57/0.96  % (25377)------------------------------
% 4.57/0.96  % (25377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.57/0.96  % (25377)Termination reason: Refutation
% 4.57/0.96  
% 4.57/0.96  % (25377)Memory used [KB]: 11129
% 4.57/0.96  % (25377)Time elapsed: 0.521 s
% 4.57/0.96  % (25377)------------------------------
% 4.57/0.96  % (25377)------------------------------
% 4.57/0.96  % (25359)Success in time 0.59 s
%------------------------------------------------------------------------------
