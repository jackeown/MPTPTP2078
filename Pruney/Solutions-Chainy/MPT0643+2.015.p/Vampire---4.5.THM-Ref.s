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
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 209 expanded)
%              Number of leaves         :   10 (  68 expanded)
%              Depth                    :   23
%              Number of atoms          :  410 (1904 expanded)
%              Number of equality atoms :  148 ( 777 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(subsumption_resolution,[],[f462,f32])).

fof(f32,plain,(
    k6_relat_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k6_relat_1(sK0) != sK2
    & sK1 = k5_relat_1(sK2,sK1)
    & v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK2),sK0)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k1_relat_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK0) != X2
          & sK1 = k5_relat_1(X2,sK1)
          & v2_funct_1(sK1)
          & r1_tarski(k2_relat_1(X2),sK0)
          & k1_relat_1(X2) = sK0
          & sK0 = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( k6_relat_1(sK0) != X2
        & sK1 = k5_relat_1(X2,sK1)
        & v2_funct_1(sK1)
        & r1_tarski(k2_relat_1(X2),sK0)
        & k1_relat_1(X2) = sK0
        & sK0 = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_relat_1(sK0) != sK2
      & sK1 = k5_relat_1(sK2,sK1)
      & v2_funct_1(sK1)
      & r1_tarski(k2_relat_1(sK2),sK0)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k1_relat_1(sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f462,plain,(
    k6_relat_1(sK0) = sK2 ),
    inference(subsumption_resolution,[],[f458,f52])).

fof(f52,plain,(
    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f49,f27])).

fof(f27,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f458,plain,
    ( sK1 != k5_relat_1(k6_relat_1(sK0),sK1)
    | k6_relat_1(sK0) = sK2 ),
    inference(trivial_inequality_removal,[],[f457])).

fof(f457,plain,
    ( sK0 != sK0
    | sK1 != k5_relat_1(k6_relat_1(sK0),sK1)
    | k6_relat_1(sK0) = sK2 ),
    inference(resolution,[],[f434,f426])).

fof(f426,plain,(
    r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f425,f27])).

fof(f425,plain,
    ( sK0 != k1_relat_1(sK1)
    | r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f402,f52])).

fof(f402,plain,(
    ! [X2] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) != X2
      | r1_tarski(X2,sK0) ) ),
    inference(forward_demodulation,[],[f401,f27])).

fof(f401,plain,(
    ! [X2] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) != X2
      | r1_tarski(X2,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f395,f23])).

fof(f395,plain,(
    ! [X2] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) != X2
      | r1_tarski(X2,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f131,f24])).

fof(f24,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X3)
      | k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != X2
      | r1_tarski(X2,k1_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f130,f36])).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f130,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != X2
      | r1_tarski(k2_relat_1(k6_relat_1(X2)),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f129,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f129,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != k1_relat_1(k6_relat_1(X2))
      | r1_tarski(k2_relat_1(k6_relat_1(X2)),k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f124,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f124,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != k1_relat_1(k6_relat_1(X2))
      | r1_tarski(k2_relat_1(k6_relat_1(X2)),k1_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f434,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 != X0
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = sK2 ) ),
    inference(forward_demodulation,[],[f433,f35])).

fof(f433,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = sK2
      | k1_relat_1(k6_relat_1(X0)) != sK0 ) ),
    inference(subsumption_resolution,[],[f432,f33])).

fof(f432,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = sK2
      | k1_relat_1(k6_relat_1(X0)) != sK0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f431,f34])).

fof(f431,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = sK2
      | k1_relat_1(k6_relat_1(X0)) != sK0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f364,f36])).

fof(f364,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | sK1 != k5_relat_1(X0,sK1)
      | sK2 = X0
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f363,f28])).

fof(f28,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f363,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f362,f31])).

fof(f31,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f362,plain,(
    ! [X0] :
      ( k5_relat_1(sK2,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f361,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f361,plain,(
    ! [X0] :
      ( k5_relat_1(sK2,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f357,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f357,plain,(
    ! [X0] :
      ( k5_relat_1(sK2,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f141,f29])).

fof(f29,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | X0 = X1
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f140,f23])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | X0 = X1
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f139,f24])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | X0 = X1
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f133,f30])).

fof(f30,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | X0 = X1
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f38,f27])).

fof(f38,plain,(
    ! [X4,X0,X3] :
      ( ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
      | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
      | k1_relat_1(X3) != k1_relat_1(X4)
      | X3 = X4
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k5_relat_1(sK3(X0),X0) = k5_relat_1(sK4(X0),X0)
            & k1_relat_1(sK3(X0)) = k1_relat_1(sK4(X0))
            & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
            & v1_funct_1(sK4(X0))
            & v1_relat_1(sK4(X0))
            & v1_funct_1(sK3(X0))
            & v1_relat_1(sK3(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                  | k1_relat_1(X3) != k1_relat_1(X4)
                  | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                  | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f21,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
              & k1_relat_1(X1) = k1_relat_1(X2)
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK3(X0) != X2
            & k5_relat_1(X2,X0) = k5_relat_1(sK3(X0),X0)
            & k1_relat_1(X2) = k1_relat_1(sK3(X0))
            & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK3(X0) != X2
          & k5_relat_1(X2,X0) = k5_relat_1(sK3(X0),X0)
          & k1_relat_1(X2) = k1_relat_1(sK3(X0))
          & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK3(X0) != sK4(X0)
        & k5_relat_1(sK3(X0),X0) = k5_relat_1(sK4(X0),X0)
        & k1_relat_1(sK3(X0)) = k1_relat_1(sK4(X0))
        & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
        & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                  & k1_relat_1(X1) = k1_relat_1(X2)
                  & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                  & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              & v1_funct_1(X1)
              & v1_relat_1(X1) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                  | k1_relat_1(X3) != k1_relat_1(X4)
                  | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                  | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                  & k1_relat_1(X1) = k1_relat_1(X2)
                  & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                  & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              & v1_funct_1(X1)
              & v1_relat_1(X1) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                  | k1_relat_1(X1) != k1_relat_1(X2)
                  | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                  | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) )
              | ~ v1_funct_1(X1)
              | ~ v1_relat_1(X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (868)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  % (868)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (876)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f463,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f462,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k6_relat_1(sK0) != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    (k6_relat_1(sK0) != sK2 & sK1 = k5_relat_1(sK2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK2),sK0) & sK0 = k1_relat_1(sK2) & sK0 = k1_relat_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK0) != X2 & sK1 = k5_relat_1(X2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(X2),sK0) & k1_relat_1(X2) = sK0 & sK0 = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X2] : (k6_relat_1(sK0) != X2 & sK1 = k5_relat_1(X2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(X2),sK0) & k1_relat_1(X2) = sK0 & sK0 = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(sK0) != sK2 & sK1 = k5_relat_1(sK2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK2),sK0) & sK0 = k1_relat_1(sK2) & sK0 = k1_relat_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    k6_relat_1(sK0) = sK2),
% 0.21/0.49    inference(subsumption_resolution,[],[f458,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    sK1 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f49,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.21/0.49    inference(resolution,[],[f37,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.49  fof(f458,plain,(
% 0.21/0.49    sK1 != k5_relat_1(k6_relat_1(sK0),sK1) | k6_relat_1(sK0) = sK2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f457])).
% 0.21/0.49  fof(f457,plain,(
% 0.21/0.49    sK0 != sK0 | sK1 != k5_relat_1(k6_relat_1(sK0),sK1) | k6_relat_1(sK0) = sK2),
% 0.21/0.49    inference(resolution,[],[f434,f426])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    r1_tarski(sK0,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f425,f27])).
% 0.21/0.49  fof(f425,plain,(
% 0.21/0.49    sK0 != k1_relat_1(sK1) | r1_tarski(sK0,sK0)),
% 0.21/0.49    inference(superposition,[],[f402,f52])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) != X2 | r1_tarski(X2,sK0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f401,f27])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) != X2 | r1_tarski(X2,k1_relat_1(sK1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f395,f23])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),sK1)) != X2 | r1_tarski(X2,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.49    inference(resolution,[],[f131,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v1_funct_1(X3) | k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != X2 | r1_tarski(X2,k1_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f130,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != X2 | r1_tarski(k2_relat_1(k6_relat_1(X2)),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f129,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != k1_relat_1(k6_relat_1(X2)) | r1_tarski(k2_relat_1(k6_relat_1(X2)),k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)) != k1_relat_1(k6_relat_1(X2)) | r1_tarski(k2_relat_1(k6_relat_1(X2)),k1_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(resolution,[],[f48,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 != X0 | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = sK2) )),
% 0.21/0.49    inference(forward_demodulation,[],[f433,f35])).
% 0.21/0.49  fof(f433,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = sK2 | k1_relat_1(k6_relat_1(X0)) != sK0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f432,f33])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = sK2 | k1_relat_1(k6_relat_1(X0)) != sK0 | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f431,f34])).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = sK2 | k1_relat_1(k6_relat_1(X0)) != sK0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(superposition,[],[f364,f36])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f363,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~r1_tarski(k2_relat_1(X0),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f362,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(sK2,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~r1_tarski(k2_relat_1(X0),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f361,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(sK2,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~r1_tarski(k2_relat_1(X0),sK0) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f357,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(sK2,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~r1_tarski(k2_relat_1(X0),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f141,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(X1) | X0 = X1 | ~r1_tarski(k2_relat_1(X1),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f23])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(X1) | X0 = X1 | ~r1_tarski(k2_relat_1(X1),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f139,f24])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(X1) | X0 = X1 | ~r1_tarski(k2_relat_1(X1),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | k1_relat_1(X0) != k1_relat_1(X1) | X0 = X1 | ~r1_tarski(k2_relat_1(X1),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.49    inference(superposition,[],[f38,f27])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X4,X0,X3] : (~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | X3 = X4 | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (((v2_funct_1(X0) | ((sK3(X0) != sK4(X0) & k5_relat_1(sK3(X0),X0) = k5_relat_1(sK4(X0),X0) & k1_relat_1(sK3(X0)) = k1_relat_1(sK4(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f21,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK3(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (? [X2] : (sK3(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK3(X0) != sK4(X0) & k5_relat_1(sK3(X0),X0) = k5_relat_1(sK4(X0),X0) & k1_relat_1(sK3(X0)) = k1_relat_1(sK4(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (((v2_funct_1(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (((v2_funct_1(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (868)------------------------------
% 0.21/0.49  % (868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (868)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (868)Memory used [KB]: 10874
% 0.21/0.49  % (868)Time elapsed: 0.063 s
% 0.21/0.49  % (868)------------------------------
% 0.21/0.49  % (868)------------------------------
% 0.21/0.50  % (857)Success in time 0.136 s
%------------------------------------------------------------------------------
