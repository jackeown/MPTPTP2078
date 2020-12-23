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
% DateTime   : Thu Dec  3 12:49:59 EST 2020

% Result     : Theorem 3.99s
% Output     : Refutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 202 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 ( 416 expanded)
%              Number of equality atoms :   56 ( 146 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2240,f44])).

fof(f44,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f2240,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    inference(superposition,[],[f347,f2232])).

fof(f2232,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) ),
    inference(resolution,[],[f1045,f2179])).

fof(f2179,plain,(
    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) ),
    inference(resolution,[],[f706,f319])).

fof(f319,plain,(
    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2)) ),
    inference(superposition,[],[f285,f309])).

fof(f309,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) ),
    inference(resolution,[],[f143,f43])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f138,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f285,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) ),
    inference(superposition,[],[f84,f118])).

fof(f118,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f84,plain,(
    ! [X2,X1] : r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f706,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),k6_relat_1(X1))
      | r1_tarski(X0,k9_relat_1(k6_relat_1(X1),X0)) ) ),
    inference(resolution,[],[f174,f45])).

fof(f174,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k9_relat_1(X3,X2)) ) ),
    inference(subsumption_resolution,[],[f172,f45])).

fof(f172,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k9_relat_1(X3,X2))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f59,f105])).

fof(f105,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f104,f47])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f104,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f102,f46])).

fof(f102,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f49,f45])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f1045,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X9,k9_relat_1(k6_relat_1(X8),X9))
      | k9_relat_1(k6_relat_1(X8),X9) = X9 ) ),
    inference(forward_demodulation,[],[f1044,f992])).

fof(f992,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(superposition,[],[f438,f105])).

fof(f438,plain,(
    ! [X2,X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f428,f118])).

fof(f428,plain,(
    ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) ),
    inference(resolution,[],[f165,f45])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) ) ),
    inference(resolution,[],[f58,f45])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f1044,plain,(
    ! [X8,X9] :
      ( k9_relat_1(k6_relat_1(X8),X9) = X9
      | ~ r1_tarski(X9,k9_relat_1(k7_relat_1(k6_relat_1(X8),X9),X9)) ) ),
    inference(forward_demodulation,[],[f1026,f992])).

fof(f1026,plain,(
    ! [X8,X9] :
      ( k9_relat_1(k7_relat_1(k6_relat_1(X8),X9),X9) = X9
      | ~ r1_tarski(X9,k9_relat_1(k7_relat_1(k6_relat_1(X8),X9),X9)) ) ),
    inference(resolution,[],[f507,f285])).

fof(f507,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_relat_1(X0))
      | k9_relat_1(X1,X0) = X0
      | ~ r1_tarski(X0,k9_relat_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f506,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_relat_1(X1))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f76,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k6_relat_1(X2)))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f506,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = X0
      | ~ r1_tarski(X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f498,f45])).

fof(f498,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = X0
      | ~ r1_tarski(X1,k6_relat_1(X0)) ) ),
    inference(superposition,[],[f151,f105])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X0,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k9_relat_1(X0,X2) = k9_relat_1(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f59,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f347,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f338,f121])).

fof(f121,plain,(
    ! [X6] : k7_relat_1(sK0,X6) = k5_relat_1(k6_relat_1(X6),sK0) ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f338,plain,(
    ! [X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f170,f45])).

fof(f170,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | k9_relat_1(k5_relat_1(X15,sK0),X16) = k9_relat_1(sK0,k9_relat_1(X15,X16)) ) ),
    inference(resolution,[],[f58,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (2602)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (2604)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (2611)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (2603)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (2601)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (2600)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (2610)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (2619)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  % (2621)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (2618)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (2599)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (2623)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (2607)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (2617)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.58  % (2608)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.58  % (2609)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.58  % (2620)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.59  % (2612)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.59  % (2622)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.60  % (2613)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.77/0.60  % (2614)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.77/0.61  % (2605)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.77/0.61  % (2606)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 2.02/0.62  % (2616)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.02/0.63  % (2615)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.02/0.63  % (2624)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.86/0.77  % (2608)Refutation not found, incomplete strategy% (2608)------------------------------
% 2.86/0.77  % (2608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.77  % (2608)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.77  
% 2.86/0.77  % (2608)Memory used [KB]: 6140
% 2.86/0.77  % (2608)Time elapsed: 0.337 s
% 2.86/0.77  % (2608)------------------------------
% 2.86/0.77  % (2608)------------------------------
% 3.99/0.88  % (2615)Refutation found. Thanks to Tanya!
% 3.99/0.88  % SZS status Theorem for theBenchmark
% 3.99/0.88  % SZS output start Proof for theBenchmark
% 3.99/0.88  fof(f2245,plain,(
% 3.99/0.88    $false),
% 3.99/0.88    inference(subsumption_resolution,[],[f2240,f44])).
% 3.99/0.88  fof(f44,plain,(
% 3.99/0.88    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 3.99/0.88    inference(cnf_transformation,[],[f38])).
% 3.99/0.88  fof(f38,plain,(
% 3.99/0.88    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 3.99/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37,f36])).
% 3.99/0.88  fof(f36,plain,(
% 3.99/0.88    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 3.99/0.88    introduced(choice_axiom,[])).
% 3.99/0.88  fof(f37,plain,(
% 3.99/0.88    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 3.99/0.88    introduced(choice_axiom,[])).
% 3.99/0.88  fof(f20,plain,(
% 3.99/0.88    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 3.99/0.88    inference(ennf_transformation,[],[f19])).
% 3.99/0.88  fof(f19,negated_conjecture,(
% 3.99/0.88    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 3.99/0.88    inference(negated_conjecture,[],[f18])).
% 3.99/0.88  fof(f18,conjecture,(
% 3.99/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 3.99/0.88  fof(f2240,plain,(
% 3.99/0.88    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 3.99/0.88    inference(superposition,[],[f347,f2232])).
% 3.99/0.88  fof(f2232,plain,(
% 3.99/0.88    sK1 = k9_relat_1(k6_relat_1(sK2),sK1)),
% 3.99/0.88    inference(resolution,[],[f1045,f2179])).
% 3.99/0.88  fof(f2179,plain,(
% 3.99/0.88    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))),
% 3.99/0.88    inference(resolution,[],[f706,f319])).
% 3.99/0.88  fof(f319,plain,(
% 3.99/0.88    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2))),
% 3.99/0.88    inference(superposition,[],[f285,f309])).
% 3.99/0.88  fof(f309,plain,(
% 3.99/0.88    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)),
% 3.99/0.88    inference(resolution,[],[f143,f43])).
% 3.99/0.88  fof(f43,plain,(
% 3.99/0.88    r1_tarski(sK1,sK2)),
% 3.99/0.88    inference(cnf_transformation,[],[f38])).
% 3.99/0.88  fof(f143,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.99/0.88    inference(forward_demodulation,[],[f138,f46])).
% 3.99/0.88  fof(f46,plain,(
% 3.99/0.88    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.99/0.88    inference(cnf_transformation,[],[f12])).
% 3.99/0.88  fof(f12,axiom,(
% 3.99/0.88    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.99/0.88  fof(f138,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.99/0.88    inference(resolution,[],[f57,f45])).
% 3.99/0.88  fof(f45,plain,(
% 3.99/0.88    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.99/0.88    inference(cnf_transformation,[],[f6])).
% 3.99/0.88  fof(f6,axiom,(
% 3.99/0.88    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.99/0.88  fof(f57,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 3.99/0.88    inference(cnf_transformation,[],[f30])).
% 3.99/0.88  fof(f30,plain,(
% 3.99/0.88    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(flattening,[],[f29])).
% 3.99/0.88  fof(f29,plain,(
% 3.99/0.88    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(ennf_transformation,[],[f16])).
% 3.99/0.88  fof(f16,axiom,(
% 3.99/0.88    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 3.99/0.88  fof(f285,plain,(
% 3.99/0.88    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))) )),
% 3.99/0.88    inference(superposition,[],[f84,f118])).
% 3.99/0.88  fof(f118,plain,(
% 3.99/0.88    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.99/0.88    inference(resolution,[],[f53,f45])).
% 3.99/0.88  fof(f53,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f26])).
% 3.99/0.88  fof(f26,plain,(
% 3.99/0.88    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(ennf_transformation,[],[f15])).
% 3.99/0.88  fof(f15,axiom,(
% 3.99/0.88    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.99/0.88  fof(f84,plain,(
% 3.99/0.88    ( ! [X2,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))) )),
% 3.99/0.88    inference(resolution,[],[f55,f45])).
% 3.99/0.88  fof(f55,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f28])).
% 3.99/0.88  fof(f28,plain,(
% 3.99/0.88    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(ennf_transformation,[],[f13])).
% 3.99/0.88  fof(f13,axiom,(
% 3.99/0.88    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 3.99/0.88  fof(f706,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),k6_relat_1(X1)) | r1_tarski(X0,k9_relat_1(k6_relat_1(X1),X0))) )),
% 3.99/0.88    inference(resolution,[],[f174,f45])).
% 3.99/0.88  fof(f174,plain,(
% 3.99/0.88    ( ! [X2,X3] : (~v1_relat_1(X3) | ~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k9_relat_1(X3,X2))) )),
% 3.99/0.88    inference(subsumption_resolution,[],[f172,f45])).
% 3.99/0.88  fof(f172,plain,(
% 3.99/0.88    ( ! [X2,X3] : (r1_tarski(X2,k9_relat_1(X3,X2)) | ~r1_tarski(k6_relat_1(X2),X3) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2))) )),
% 3.99/0.88    inference(superposition,[],[f59,f105])).
% 3.99/0.88  fof(f105,plain,(
% 3.99/0.88    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 3.99/0.88    inference(forward_demodulation,[],[f104,f47])).
% 3.99/0.88  fof(f47,plain,(
% 3.99/0.88    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.99/0.88    inference(cnf_transformation,[],[f12])).
% 3.99/0.88  fof(f104,plain,(
% 3.99/0.88    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 3.99/0.88    inference(forward_demodulation,[],[f102,f46])).
% 3.99/0.88  fof(f102,plain,(
% 3.99/0.88    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 3.99/0.88    inference(resolution,[],[f49,f45])).
% 3.99/0.88  fof(f49,plain,(
% 3.99/0.88    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f22])).
% 3.99/0.88  fof(f22,plain,(
% 3.99/0.88    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.99/0.88    inference(ennf_transformation,[],[f8])).
% 3.99/0.88  fof(f8,axiom,(
% 3.99/0.88    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 3.99/0.88  fof(f59,plain,(
% 3.99/0.88    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f33])).
% 3.99/0.88  fof(f33,plain,(
% 3.99/0.88    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(flattening,[],[f32])).
% 3.99/0.88  fof(f32,plain,(
% 3.99/0.88    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(ennf_transformation,[],[f10])).
% 3.99/0.88  fof(f10,axiom,(
% 3.99/0.88    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 3.99/0.88  fof(f1045,plain,(
% 3.99/0.88    ( ! [X8,X9] : (~r1_tarski(X9,k9_relat_1(k6_relat_1(X8),X9)) | k9_relat_1(k6_relat_1(X8),X9) = X9) )),
% 3.99/0.88    inference(forward_demodulation,[],[f1044,f992])).
% 3.99/0.88  fof(f992,plain,(
% 3.99/0.88    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 3.99/0.88    inference(superposition,[],[f438,f105])).
% 3.99/0.88  fof(f438,plain,(
% 3.99/0.88    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 3.99/0.88    inference(forward_demodulation,[],[f428,f118])).
% 3.99/0.88  fof(f428,plain,(
% 3.99/0.88    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) )),
% 3.99/0.88    inference(resolution,[],[f165,f45])).
% 3.99/0.88  fof(f165,plain,(
% 3.99/0.88    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2))) )),
% 3.99/0.88    inference(resolution,[],[f58,f45])).
% 3.99/0.88  fof(f58,plain,(
% 3.99/0.88    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f31])).
% 3.99/0.88  fof(f31,plain,(
% 3.99/0.88    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.99/0.88    inference(ennf_transformation,[],[f11])).
% 3.99/0.88  fof(f11,axiom,(
% 3.99/0.88    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 3.99/0.88  fof(f1044,plain,(
% 3.99/0.88    ( ! [X8,X9] : (k9_relat_1(k6_relat_1(X8),X9) = X9 | ~r1_tarski(X9,k9_relat_1(k7_relat_1(k6_relat_1(X8),X9),X9))) )),
% 3.99/0.88    inference(forward_demodulation,[],[f1026,f992])).
% 3.99/0.88  fof(f1026,plain,(
% 3.99/0.88    ( ! [X8,X9] : (k9_relat_1(k7_relat_1(k6_relat_1(X8),X9),X9) = X9 | ~r1_tarski(X9,k9_relat_1(k7_relat_1(k6_relat_1(X8),X9),X9))) )),
% 3.99/0.88    inference(resolution,[],[f507,f285])).
% 3.99/0.88  fof(f507,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | k9_relat_1(X1,X0) = X0 | ~r1_tarski(X0,k9_relat_1(X1,X0))) )),
% 3.99/0.88    inference(subsumption_resolution,[],[f506,f186])).
% 3.99/0.88  fof(f186,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k6_relat_1(X1)) | v1_relat_1(X0)) )),
% 3.99/0.88    inference(resolution,[],[f76,f65])).
% 3.99/0.88  fof(f65,plain,(
% 3.99/0.88    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f41])).
% 3.99/0.88  fof(f41,plain,(
% 3.99/0.88    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.99/0.88    inference(nnf_transformation,[],[f4])).
% 3.99/0.88  fof(f4,axiom,(
% 3.99/0.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.99/0.88  fof(f76,plain,(
% 3.99/0.88    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k6_relat_1(X2))) | v1_relat_1(X1)) )),
% 3.99/0.88    inference(resolution,[],[f50,f45])).
% 3.99/0.88  fof(f50,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f23])).
% 3.99/0.88  fof(f23,plain,(
% 3.99/0.88    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.99/0.88    inference(ennf_transformation,[],[f5])).
% 3.99/0.88  fof(f5,axiom,(
% 3.99/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.99/0.88  fof(f506,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k9_relat_1(X1,X0)) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = X0 | ~r1_tarski(X1,k6_relat_1(X0))) )),
% 3.99/0.88    inference(subsumption_resolution,[],[f498,f45])).
% 3.99/0.88  fof(f498,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(X0,k9_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = X0 | ~r1_tarski(X1,k6_relat_1(X0))) )),
% 3.99/0.88    inference(superposition,[],[f151,f105])).
% 3.99/0.88  fof(f151,plain,(
% 3.99/0.88    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X0,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k9_relat_1(X0,X2) = k9_relat_1(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.99/0.88    inference(resolution,[],[f59,f63])).
% 3.99/0.88  fof(f63,plain,(
% 3.99/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.99/0.88    inference(cnf_transformation,[],[f40])).
% 3.99/0.88  fof(f40,plain,(
% 3.99/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/0.88    inference(flattening,[],[f39])).
% 3.99/0.88  fof(f39,plain,(
% 3.99/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/0.88    inference(nnf_transformation,[],[f1])).
% 3.99/0.88  fof(f1,axiom,(
% 3.99/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.99/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.99/0.88  fof(f347,plain,(
% 3.99/0.88    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1))) )),
% 3.99/0.88    inference(forward_demodulation,[],[f338,f121])).
% 3.99/0.88  fof(f121,plain,(
% 3.99/0.88    ( ! [X6] : (k7_relat_1(sK0,X6) = k5_relat_1(k6_relat_1(X6),sK0)) )),
% 3.99/0.88    inference(resolution,[],[f53,f42])).
% 3.99/0.88  fof(f42,plain,(
% 3.99/0.88    v1_relat_1(sK0)),
% 3.99/0.88    inference(cnf_transformation,[],[f38])).
% 3.99/0.88  fof(f338,plain,(
% 3.99/0.88    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1))) )),
% 3.99/0.88    inference(resolution,[],[f170,f45])).
% 3.99/0.88  fof(f170,plain,(
% 3.99/0.88    ( ! [X15,X16] : (~v1_relat_1(X15) | k9_relat_1(k5_relat_1(X15,sK0),X16) = k9_relat_1(sK0,k9_relat_1(X15,X16))) )),
% 3.99/0.88    inference(resolution,[],[f58,f42])).
% 3.99/0.88  % SZS output end Proof for theBenchmark
% 3.99/0.88  % (2615)------------------------------
% 3.99/0.88  % (2615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/0.88  % (2615)Termination reason: Refutation
% 3.99/0.88  
% 3.99/0.88  % (2615)Memory used [KB]: 3454
% 3.99/0.88  % (2615)Time elapsed: 0.440 s
% 3.99/0.88  % (2615)------------------------------
% 3.99/0.88  % (2615)------------------------------
% 3.99/0.89  % (2598)Success in time 0.525 s
%------------------------------------------------------------------------------
