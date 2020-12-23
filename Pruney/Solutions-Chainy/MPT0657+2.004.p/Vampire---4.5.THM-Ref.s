%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 586 expanded)
%              Number of leaves         :    7 ( 106 expanded)
%              Depth                    :   27
%              Number of atoms          :  266 (3251 expanded)
%              Number of equality atoms :  111 (1240 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(subsumption_resolution,[],[f263,f31])).

fof(f31,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f263,plain,(
    sK1 = k2_funct_1(sK0) ),
    inference(forward_demodulation,[],[f262,f241])).

fof(f241,plain,(
    sK0 = k2_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | sK0 = k2_funct_1(sK1) ),
    inference(forward_demodulation,[],[f239,f109])).

fof(f109,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f108,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f108,plain,(
    k1_relat_1(sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f107,f30])).

fof(f30,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f107,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f104,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(subsumption_resolution,[],[f84,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK1))
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(superposition,[],[f38,f29])).

fof(f29,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f239,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | sK0 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f238,f26])).

fof(f238,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f237,f29])).

fof(f237,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f236,f33])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f236,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f235,f32])).

fof(f235,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f230,f27])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f230,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(superposition,[],[f52,f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
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
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f262,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f261,f32])).

fof(f261,plain,
    ( ~ v1_relat_1(sK0)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f260,f241])).

fof(f260,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f259,f109])).

fof(f259,plain,
    ( k2_relat_1(sK0) != k1_relat_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f258,f241])).

fof(f258,plain,
    ( k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f257,f33])).

fof(f257,plain,
    ( ~ v1_funct_1(sK0)
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f256,f241])).

fof(f256,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,
    ( k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f254,f29])).

fof(f254,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f253,f241])).

fof(f253,plain,
    ( k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f252,f27])).

fof(f252,plain,
    ( k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f234,f26])).

fof(f234,plain,
    ( k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(superposition,[],[f52,f199])).

fof(f199,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(subsumption_resolution,[],[f198,f197])).

fof(f197,plain,(
    v2_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | v2_funct_1(sK1) ),
    inference(forward_demodulation,[],[f191,f109])).

fof(f191,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f190,f26])).

fof(f190,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f189,f33])).

fof(f189,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f188,f32])).

fof(f188,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f185,f27])).

fof(f185,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(superposition,[],[f43,f30])).

fof(f198,plain,
    ( ~ v2_funct_1(sK1)
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f78,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f42,f27])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (4307)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (4328)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (4311)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (4311)Refutation not found, incomplete strategy% (4311)------------------------------
% 0.22/0.51  % (4311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4311)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4311)Memory used [KB]: 6140
% 0.22/0.51  % (4311)Time elapsed: 0.086 s
% 0.22/0.51  % (4311)------------------------------
% 0.22/0.51  % (4311)------------------------------
% 0.22/0.51  % (4329)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (4319)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (4331)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (4312)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (4317)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (4312)Refutation not found, incomplete strategy% (4312)------------------------------
% 0.22/0.51  % (4312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4312)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4312)Memory used [KB]: 10618
% 0.22/0.51  % (4312)Time elapsed: 0.092 s
% 0.22/0.51  % (4312)------------------------------
% 0.22/0.51  % (4312)------------------------------
% 0.22/0.52  % (4328)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (4319)Refutation not found, incomplete strategy% (4319)------------------------------
% 0.22/0.52  % (4319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4319)Memory used [KB]: 6268
% 0.22/0.52  % (4319)Time elapsed: 0.102 s
% 0.22/0.52  % (4319)------------------------------
% 0.22/0.52  % (4319)------------------------------
% 0.22/0.52  % (4322)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f263,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    sK1 != k2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    sK1 = k2_funct_1(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f262,f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f240])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f239,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f108,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    k1_relat_1(sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.22/0.52    inference(forward_demodulation,[],[f107,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.52    inference(resolution,[],[f98,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f84,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0))) )),
% 0.22/0.52    inference(superposition,[],[f38,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f238,f26])).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f237,f29])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | k1_relat_1(sK0) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f236,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK0) | k1_relat_1(sK0) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f235,f32])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k1_relat_1(sK0) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f230,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k1_relat_1(sK0) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(superposition,[],[f52,f30])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f44,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f261,f32])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f260,f241])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f259,f109])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    k2_relat_1(sK0) != k1_relat_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f258,f241])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f257,f33])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    ~v1_funct_1(sK0) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f256,f241])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    ~v1_funct_1(k2_funct_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f255])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f254,f29])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f253,f241])).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f252,f27])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f234,f26])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.52    inference(superposition,[],[f52,f199])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f198,f197])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    v2_funct_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f196])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | v2_funct_1(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f191,f109])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f26])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f189,f33])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f188,f32])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f185,f27])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(superposition,[],[f43,f30])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    ~v2_funct_1(sK1) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f78,f26])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.22/0.52    inference(resolution,[],[f42,f27])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (4328)------------------------------
% 0.22/0.52  % (4328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4328)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (4328)Memory used [KB]: 10746
% 0.22/0.52  % (4328)Time elapsed: 0.105 s
% 0.22/0.52  % (4328)------------------------------
% 0.22/0.52  % (4328)------------------------------
% 0.22/0.52  % (4320)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (4305)Success in time 0.155 s
%------------------------------------------------------------------------------
