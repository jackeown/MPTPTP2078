%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:11 EST 2020

% Result     : Theorem 4.52s
% Output     : Refutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 595 expanded)
%              Number of leaves         :   14 ( 115 expanded)
%              Depth                    :   25
%              Number of atoms          :  312 (2805 expanded)
%              Number of equality atoms :  103 (1048 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1010,f5499])).

fof(f5499,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f5498])).

fof(f5498,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f5495,f2829])).

fof(f2829,plain,
    ( k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2828,f52])).

fof(f52,plain,(
    sK1 != k7_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
                & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
             => k7_relat_1(X2,X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(f2828,plain,
    ( k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0)))
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2827,f53])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f2827,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0)))
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2824,f54])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f2824,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0)))
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(equality_resolution,[],[f1014])).

fof(f1014,plain,
    ( ! [X5] :
        ( k1_relat_1(sK1) != k1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X5)
        | k1_funct_1(X5,sK3(X5,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(X5,k7_relat_1(sK2,sK0)))
        | k7_relat_1(sK2,sK0) = X5 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f467,f998])).

fof(f998,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f997])).

fof(f997,plain,
    ( spl4_1
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f467,plain,(
    ! [X5] :
      ( k1_relat_1(sK1) != k1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(X5)
      | k1_funct_1(X5,sK3(X5,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(X5,k7_relat_1(sK2,sK0)))
      | k7_relat_1(sK2,sK0) = X5 ) ),
    inference(subsumption_resolution,[],[f128,f465])).

fof(f465,plain,(
    v1_funct_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f464,f49])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f464,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k7_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f463,f84])).

fof(f84,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f49,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f463,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f462,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f462,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f461,f84])).

fof(f461,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_funct_1(k7_relat_1(sK2,k1_relat_1(sK2)))
    | ~ v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f457,f285])).

fof(f285,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(superposition,[],[f159,f117])).

fof(f117,plain,(
    k1_relat_1(sK1) = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f86,f51])).

fof(f51,plain,(
    k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X5] : k1_relat_1(k7_relat_1(sK2,X5)) = k3_xboole_0(k1_relat_1(sK2),X5) ),
    inference(resolution,[],[f49,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f159,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f150,f86])).

fof(f150,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X0)) ),
    inference(superposition,[],[f85,f84])).

fof(f85,plain,(
    ! [X4,X3] : k7_relat_1(k7_relat_1(sK2,X3),X4) = k7_relat_1(sK2,k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f457,plain,
    ( v1_funct_1(k7_relat_1(sK2,k1_relat_1(sK1)))
    | ~ v1_funct_1(k7_relat_1(sK2,k1_relat_1(sK2)))
    | ~ v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(superposition,[],[f157,f51])).

fof(f157,plain,(
    ! [X10,X11] :
      ( v1_funct_1(k7_relat_1(sK2,k3_xboole_0(X10,X11)))
      | ~ v1_funct_1(k7_relat_1(sK2,X10))
      | ~ v1_relat_1(k7_relat_1(sK2,X10)) ) ),
    inference(superposition,[],[f65,f85])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f128,plain,(
    ! [X5] :
      ( k1_relat_1(sK1) != k1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | ~ v1_funct_1(k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(X5)
      | k1_funct_1(X5,sK3(X5,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(X5,k7_relat_1(sK2,sK0)))
      | k7_relat_1(sK2,sK0) = X5 ) ),
    inference(superposition,[],[f61,f117])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f5495,plain,
    ( k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0)))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f4643,f5494])).

fof(f5494,plain,
    ( k7_relat_1(sK2,sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f5485,f1054])).

fof(f1054,plain,
    ( k7_relat_1(sK2,sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k7_relat_1(sK2,sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1024,f117])).

fof(f1024,plain,
    ( k7_relat_1(sK2,sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f998,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f5485,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f1410,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1410,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k5_relat_1(k6_relat_1(X0),sK2) = k5_relat_1(k6_relat_1(X0),k7_relat_1(sK2,sK0)) ) ),
    inference(subsumption_resolution,[],[f1409,f66])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f1409,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k5_relat_1(k6_relat_1(X0),sK2) = k5_relat_1(k6_relat_1(X0),k7_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f135,f71])).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,sK2) = k5_relat_1(X0,k7_relat_1(sK2,sK0)) ) ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,sK2) = k5_relat_1(X0,k7_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f68,f117])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

fof(f4643,plain,
    ( k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),sK3(sK1,k7_relat_1(sK2,sK0)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f4642,f2271])).

fof(f2271,plain,
    ( k1_funct_1(sK2,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f2119,f48])).

fof(f48,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2119,plain,
    ( r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2118,f52])).

fof(f2118,plain,
    ( r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1))
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2117,f53])).

fof(f2117,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1))
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2114,f54])).

fof(f2114,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1))
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(equality_resolution,[],[f1016])).

fof(f1016,plain,
    ( ! [X3] :
        ( k1_relat_1(sK1) != k1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | r2_hidden(sK3(X3,k7_relat_1(sK2,sK0)),k1_relat_1(X3))
        | k7_relat_1(sK2,sK0) = X3 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f469,f998])).

fof(f469,plain,(
    ! [X3] :
      ( k1_relat_1(sK1) != k1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(X3)
      | r2_hidden(sK3(X3,k7_relat_1(sK2,sK0)),k1_relat_1(X3))
      | k7_relat_1(sK2,sK0) = X3 ) ),
    inference(subsumption_resolution,[],[f126,f465])).

fof(f126,plain,(
    ! [X3] :
      ( k1_relat_1(sK1) != k1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | ~ v1_funct_1(k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(X3)
      | r2_hidden(sK3(X3,k7_relat_1(sK2,sK0)),k1_relat_1(X3))
      | k7_relat_1(sK2,sK0) = X3 ) ),
    inference(superposition,[],[f60,f117])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4642,plain,
    ( k1_funct_1(sK2,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),sK3(sK1,k7_relat_1(sK2,sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f781,f2119])).

fof(f781,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),X1) ) ),
    inference(forward_demodulation,[],[f757,f117])).

fof(f757,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,sK0)))
      | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),X1) ) ),
    inference(superposition,[],[f121,f285])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ) ),
    inference(subsumption_resolution,[],[f120,f49])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ) ),
    inference(superposition,[],[f59,f86])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f1010,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1005,f49])).

fof(f1005,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f999,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f999,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f997])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6195)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (6187)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (6177)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (6178)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (6179)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (6173)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (6172)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (6175)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (6194)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (6176)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (6174)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (6191)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (6196)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (6200)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (6188)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (6201)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (6188)Refutation not found, incomplete strategy% (6188)------------------------------
% 0.20/0.54  % (6188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6188)Memory used [KB]: 10746
% 0.20/0.54  % (6188)Time elapsed: 0.139 s
% 0.20/0.54  % (6188)------------------------------
% 0.20/0.54  % (6188)------------------------------
% 0.20/0.54  % (6192)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (6181)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (6180)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (6193)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (6184)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (6183)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (6182)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (6186)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (6185)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (6197)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (6198)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (6190)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (6199)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.57  % (6189)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 3.09/0.78  % (6224)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.09/0.81  % (6196)Time limit reached!
% 3.09/0.81  % (6196)------------------------------
% 3.09/0.81  % (6196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.81  % (6196)Termination reason: Time limit
% 3.09/0.81  
% 3.09/0.81  % (6196)Memory used [KB]: 13304
% 3.09/0.81  % (6196)Time elapsed: 0.401 s
% 3.09/0.81  % (6196)------------------------------
% 3.09/0.81  % (6196)------------------------------
% 3.09/0.84  % (6174)Time limit reached!
% 3.09/0.84  % (6174)------------------------------
% 3.09/0.84  % (6174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.84  % (6174)Termination reason: Time limit
% 3.09/0.84  % (6174)Termination phase: Saturation
% 3.09/0.84  
% 3.09/0.84  % (6174)Memory used [KB]: 6780
% 3.09/0.84  % (6174)Time elapsed: 0.436 s
% 3.09/0.84  % (6174)------------------------------
% 3.09/0.84  % (6174)------------------------------
% 4.11/0.91  % (6201)Time limit reached!
% 4.11/0.91  % (6201)------------------------------
% 4.11/0.91  % (6201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.91  % (6201)Termination reason: Time limit
% 4.11/0.91  % (6201)Termination phase: Saturation
% 4.11/0.91  
% 4.11/0.91  % (6201)Memory used [KB]: 2942
% 4.11/0.91  % (6201)Time elapsed: 0.500 s
% 4.11/0.91  % (6201)------------------------------
% 4.11/0.91  % (6201)------------------------------
% 4.11/0.91  % (6186)Time limit reached!
% 4.11/0.91  % (6186)------------------------------
% 4.11/0.91  % (6186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.91  % (6186)Termination reason: Time limit
% 4.11/0.91  % (6186)Termination phase: Saturation
% 4.11/0.91  
% 4.11/0.91  % (6186)Memory used [KB]: 4349
% 4.11/0.91  % (6186)Time elapsed: 0.500 s
% 4.11/0.91  % (6186)------------------------------
% 4.11/0.91  % (6186)------------------------------
% 4.11/0.93  % (6178)Time limit reached!
% 4.11/0.93  % (6178)------------------------------
% 4.11/0.93  % (6178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.93  % (6178)Termination reason: Time limit
% 4.11/0.93  % (6178)Termination phase: Saturation
% 4.11/0.93  
% 4.11/0.93  % (6178)Memory used [KB]: 14967
% 4.11/0.93  % (6178)Time elapsed: 0.500 s
% 4.11/0.93  % (6178)------------------------------
% 4.11/0.93  % (6178)------------------------------
% 4.52/0.96  % (6199)Refutation found. Thanks to Tanya!
% 4.52/0.96  % SZS status Theorem for theBenchmark
% 4.52/0.96  % SZS output start Proof for theBenchmark
% 4.52/0.96  fof(f5506,plain,(
% 4.52/0.96    $false),
% 4.52/0.96    inference(avatar_sat_refutation,[],[f1010,f5499])).
% 4.52/0.96  fof(f5499,plain,(
% 4.52/0.96    ~spl4_1),
% 4.52/0.96    inference(avatar_contradiction_clause,[],[f5498])).
% 4.52/0.96  fof(f5498,plain,(
% 4.52/0.96    $false | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f5495,f2829])).
% 4.52/0.96  fof(f2829,plain,(
% 4.52/0.96    k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0))) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f2828,f52])).
% 4.52/0.96  fof(f52,plain,(
% 4.52/0.96    sK1 != k7_relat_1(sK2,sK0)),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f26,plain,(
% 4.52/0.96    ? [X0,X1] : (? [X2] : (k7_relat_1(X2,X0) != X1 & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.52/0.96    inference(flattening,[],[f25])).
% 4.52/0.96  fof(f25,plain,(
% 4.52/0.96    ? [X0,X1] : (? [X2] : ((k7_relat_1(X2,X0) != X1 & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.52/0.96    inference(ennf_transformation,[],[f24])).
% 4.52/0.96  fof(f24,negated_conjecture,(
% 4.52/0.96    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 4.52/0.96    inference(negated_conjecture,[],[f23])).
% 4.52/0.96  fof(f23,conjecture,(
% 4.52/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).
% 4.52/0.96  fof(f2828,plain,(
% 4.52/0.96    k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0))) | sK1 = k7_relat_1(sK2,sK0) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f2827,f53])).
% 4.52/0.96  fof(f53,plain,(
% 4.52/0.96    v1_relat_1(sK1)),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f2827,plain,(
% 4.52/0.96    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0))) | sK1 = k7_relat_1(sK2,sK0) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f2824,f54])).
% 4.52/0.96  fof(f54,plain,(
% 4.52/0.96    v1_funct_1(sK1)),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f2824,plain,(
% 4.52/0.96    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0))) | sK1 = k7_relat_1(sK2,sK0) | ~spl4_1),
% 4.52/0.96    inference(equality_resolution,[],[f1014])).
% 4.52/0.96  fof(f1014,plain,(
% 4.52/0.96    ( ! [X5] : (k1_relat_1(sK1) != k1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | k1_funct_1(X5,sK3(X5,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(X5,k7_relat_1(sK2,sK0))) | k7_relat_1(sK2,sK0) = X5) ) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f467,f998])).
% 4.52/0.96  fof(f998,plain,(
% 4.52/0.96    v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl4_1),
% 4.52/0.96    inference(avatar_component_clause,[],[f997])).
% 4.52/0.96  fof(f997,plain,(
% 4.52/0.96    spl4_1 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 4.52/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.52/0.96  fof(f467,plain,(
% 4.52/0.96    ( ! [X5] : (k1_relat_1(sK1) != k1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(X5) | k1_funct_1(X5,sK3(X5,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(X5,k7_relat_1(sK2,sK0))) | k7_relat_1(sK2,sK0) = X5) )),
% 4.52/0.96    inference(subsumption_resolution,[],[f128,f465])).
% 4.52/0.96  fof(f465,plain,(
% 4.52/0.96    v1_funct_1(k7_relat_1(sK2,sK0))),
% 4.52/0.96    inference(subsumption_resolution,[],[f464,f49])).
% 4.52/0.96  fof(f49,plain,(
% 4.52/0.96    v1_relat_1(sK2)),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f464,plain,(
% 4.52/0.96    ~v1_relat_1(sK2) | v1_funct_1(k7_relat_1(sK2,sK0))),
% 4.52/0.96    inference(forward_demodulation,[],[f463,f84])).
% 4.52/0.96  fof(f84,plain,(
% 4.52/0.96    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 4.52/0.96    inference(resolution,[],[f49,f58])).
% 4.52/0.96  fof(f58,plain,(
% 4.52/0.96    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 4.52/0.96    inference(cnf_transformation,[],[f30])).
% 4.52/0.96  fof(f30,plain,(
% 4.52/0.96    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.52/0.96    inference(ennf_transformation,[],[f18])).
% 4.52/0.96  fof(f18,axiom,(
% 4.52/0.96    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 4.52/0.96  fof(f463,plain,(
% 4.52/0.96    v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),
% 4.52/0.96    inference(subsumption_resolution,[],[f462,f50])).
% 4.52/0.96  fof(f50,plain,(
% 4.52/0.96    v1_funct_1(sK2)),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f462,plain,(
% 4.52/0.96    ~v1_funct_1(sK2) | v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),
% 4.52/0.96    inference(forward_demodulation,[],[f461,f84])).
% 4.52/0.96  fof(f461,plain,(
% 4.52/0.96    v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_funct_1(k7_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),
% 4.52/0.96    inference(forward_demodulation,[],[f457,f285])).
% 4.52/0.96  fof(f285,plain,(
% 4.52/0.96    k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k1_relat_1(sK1))),
% 4.52/0.96    inference(superposition,[],[f159,f117])).
% 4.52/0.96  fof(f117,plain,(
% 4.52/0.96    k1_relat_1(sK1) = k1_relat_1(k7_relat_1(sK2,sK0))),
% 4.52/0.96    inference(superposition,[],[f86,f51])).
% 4.52/0.96  fof(f51,plain,(
% 4.52/0.96    k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0)),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f86,plain,(
% 4.52/0.96    ( ! [X5] : (k1_relat_1(k7_relat_1(sK2,X5)) = k3_xboole_0(k1_relat_1(sK2),X5)) )),
% 4.52/0.96    inference(resolution,[],[f49,f63])).
% 4.52/0.96  fof(f63,plain,(
% 4.52/0.96    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f36])).
% 4.52/0.96  fof(f36,plain,(
% 4.52/0.96    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.52/0.96    inference(ennf_transformation,[],[f15])).
% 4.52/0.96  fof(f15,axiom,(
% 4.52/0.96    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 4.52/0.96  fof(f159,plain,(
% 4.52/0.96    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.52/0.96    inference(forward_demodulation,[],[f150,f86])).
% 4.52/0.96  fof(f150,plain,(
% 4.52/0.96    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X0))) )),
% 4.52/0.96    inference(superposition,[],[f85,f84])).
% 4.52/0.96  fof(f85,plain,(
% 4.52/0.96    ( ! [X4,X3] : (k7_relat_1(k7_relat_1(sK2,X3),X4) = k7_relat_1(sK2,k3_xboole_0(X3,X4))) )),
% 4.52/0.96    inference(resolution,[],[f49,f62])).
% 4.52/0.96  fof(f62,plain,(
% 4.52/0.96    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 4.52/0.96    inference(cnf_transformation,[],[f35])).
% 4.52/0.96  fof(f35,plain,(
% 4.52/0.96    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 4.52/0.96    inference(ennf_transformation,[],[f7])).
% 4.52/0.96  fof(f7,axiom,(
% 4.52/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 4.52/0.96  fof(f457,plain,(
% 4.52/0.96    v1_funct_1(k7_relat_1(sK2,k1_relat_1(sK1))) | ~v1_funct_1(k7_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)))),
% 4.52/0.96    inference(superposition,[],[f157,f51])).
% 4.52/0.96  fof(f157,plain,(
% 4.52/0.96    ( ! [X10,X11] : (v1_funct_1(k7_relat_1(sK2,k3_xboole_0(X10,X11))) | ~v1_funct_1(k7_relat_1(sK2,X10)) | ~v1_relat_1(k7_relat_1(sK2,X10))) )),
% 4.52/0.96    inference(superposition,[],[f65,f85])).
% 4.52/0.96  fof(f65,plain,(
% 4.52/0.96    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f38])).
% 4.52/0.96  fof(f38,plain,(
% 4.52/0.96    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.52/0.96    inference(flattening,[],[f37])).
% 4.52/0.96  fof(f37,plain,(
% 4.52/0.96    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.52/0.96    inference(ennf_transformation,[],[f20])).
% 4.52/0.96  fof(f20,axiom,(
% 4.52/0.96    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 4.52/0.96  fof(f128,plain,(
% 4.52/0.96    ( ! [X5] : (k1_relat_1(sK1) != k1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(X5) | k1_funct_1(X5,sK3(X5,k7_relat_1(sK2,sK0))) != k1_funct_1(k7_relat_1(sK2,sK0),sK3(X5,k7_relat_1(sK2,sK0))) | k7_relat_1(sK2,sK0) = X5) )),
% 4.52/0.96    inference(superposition,[],[f61,f117])).
% 4.52/0.96  fof(f61,plain,(
% 4.52/0.96    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | X0 = X1) )),
% 4.52/0.96    inference(cnf_transformation,[],[f34])).
% 4.52/0.96  fof(f34,plain,(
% 4.52/0.96    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.52/0.96    inference(flattening,[],[f33])).
% 4.52/0.96  fof(f33,plain,(
% 4.52/0.96    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.52/0.96    inference(ennf_transformation,[],[f22])).
% 4.52/0.96  fof(f22,axiom,(
% 4.52/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 4.52/0.96  fof(f5495,plain,(
% 4.52/0.96    k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(k7_relat_1(sK2,sK0),sK3(sK1,k7_relat_1(sK2,sK0))) | ~spl4_1),
% 4.52/0.96    inference(backward_demodulation,[],[f4643,f5494])).
% 4.52/0.96  fof(f5494,plain,(
% 4.52/0.96    k7_relat_1(sK2,sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2) | ~spl4_1),
% 4.52/0.96    inference(forward_demodulation,[],[f5485,f1054])).
% 4.52/0.96  fof(f1054,plain,(
% 4.52/0.96    k7_relat_1(sK2,sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k7_relat_1(sK2,sK0)) | ~spl4_1),
% 4.52/0.96    inference(forward_demodulation,[],[f1024,f117])).
% 4.52/0.96  fof(f1024,plain,(
% 4.52/0.96    k7_relat_1(sK2,sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))),k7_relat_1(sK2,sK0)) | ~spl4_1),
% 4.52/0.96    inference(resolution,[],[f998,f69])).
% 4.52/0.96  fof(f69,plain,(
% 4.52/0.96    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 4.52/0.96    inference(cnf_transformation,[],[f41])).
% 4.52/0.96  fof(f41,plain,(
% 4.52/0.96    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 4.52/0.96    inference(ennf_transformation,[],[f12])).
% 4.52/0.96  fof(f12,axiom,(
% 4.52/0.96    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 4.52/0.96  fof(f5485,plain,(
% 4.52/0.96    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k7_relat_1(sK2,sK0))),
% 4.52/0.96    inference(resolution,[],[f1410,f80])).
% 4.52/0.96  fof(f80,plain,(
% 4.52/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.52/0.96    inference(equality_resolution,[],[f72])).
% 4.52/0.96  fof(f72,plain,(
% 4.52/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.52/0.96    inference(cnf_transformation,[],[f1])).
% 4.52/0.96  fof(f1,axiom,(
% 4.52/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.52/0.96  fof(f1410,plain,(
% 4.52/0.96    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k5_relat_1(k6_relat_1(X0),sK2) = k5_relat_1(k6_relat_1(X0),k7_relat_1(sK2,sK0))) )),
% 4.52/0.96    inference(subsumption_resolution,[],[f1409,f66])).
% 4.52/0.96  fof(f66,plain,(
% 4.52/0.96    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.52/0.96    inference(cnf_transformation,[],[f19])).
% 4.52/0.96  fof(f19,axiom,(
% 4.52/0.96    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 4.52/0.96  fof(f1409,plain,(
% 4.52/0.96    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(X0)) | k5_relat_1(k6_relat_1(X0),sK2) = k5_relat_1(k6_relat_1(X0),k7_relat_1(sK2,sK0))) )),
% 4.52/0.96    inference(superposition,[],[f135,f71])).
% 4.52/0.96  fof(f71,plain,(
% 4.52/0.96    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.52/0.96    inference(cnf_transformation,[],[f11])).
% 4.52/0.96  fof(f11,axiom,(
% 4.52/0.96    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 4.52/0.96  fof(f135,plain,(
% 4.52/0.96    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~v1_relat_1(X0) | k5_relat_1(X0,sK2) = k5_relat_1(X0,k7_relat_1(sK2,sK0))) )),
% 4.52/0.96    inference(subsumption_resolution,[],[f124,f49])).
% 4.52/0.96  fof(f124,plain,(
% 4.52/0.96    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | k5_relat_1(X0,sK2) = k5_relat_1(X0,k7_relat_1(sK2,sK0))) )),
% 4.52/0.96    inference(superposition,[],[f68,f117])).
% 4.52/0.96  fof(f68,plain,(
% 4.52/0.96    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f40])).
% 4.52/0.96  fof(f40,plain,(
% 4.52/0.96    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.52/0.96    inference(flattening,[],[f39])).
% 4.52/0.96  fof(f39,plain,(
% 4.52/0.96    ! [X0,X1] : (! [X2] : ((k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.52/0.96    inference(ennf_transformation,[],[f10])).
% 4.52/0.96  fof(f10,axiom,(
% 4.52/0.96    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,k7_relat_1(X2,X0)) = k5_relat_1(X1,X2))))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).
% 4.52/0.96  fof(f4643,plain,(
% 4.52/0.96    k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),sK3(sK1,k7_relat_1(sK2,sK0))) | ~spl4_1),
% 4.52/0.96    inference(forward_demodulation,[],[f4642,f2271])).
% 4.52/0.96  fof(f2271,plain,(
% 4.52/0.96    k1_funct_1(sK2,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(sK1,sK3(sK1,k7_relat_1(sK2,sK0))) | ~spl4_1),
% 4.52/0.96    inference(resolution,[],[f2119,f48])).
% 4.52/0.96  fof(f48,plain,(
% 4.52/0.96    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f26])).
% 4.52/0.96  fof(f2119,plain,(
% 4.52/0.96    r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1)) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f2118,f52])).
% 4.52/0.96  fof(f2118,plain,(
% 4.52/0.96    r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1)) | sK1 = k7_relat_1(sK2,sK0) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f2117,f53])).
% 4.52/0.96  fof(f2117,plain,(
% 4.52/0.96    ~v1_relat_1(sK1) | r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1)) | sK1 = k7_relat_1(sK2,sK0) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f2114,f54])).
% 4.52/0.96  fof(f2114,plain,(
% 4.52/0.96    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | r2_hidden(sK3(sK1,k7_relat_1(sK2,sK0)),k1_relat_1(sK1)) | sK1 = k7_relat_1(sK2,sK0) | ~spl4_1),
% 4.52/0.96    inference(equality_resolution,[],[f1016])).
% 4.52/0.96  fof(f1016,plain,(
% 4.52/0.96    ( ! [X3] : (k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | r2_hidden(sK3(X3,k7_relat_1(sK2,sK0)),k1_relat_1(X3)) | k7_relat_1(sK2,sK0) = X3) ) | ~spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f469,f998])).
% 4.52/0.96  fof(f469,plain,(
% 4.52/0.96    ( ! [X3] : (k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(X3) | r2_hidden(sK3(X3,k7_relat_1(sK2,sK0)),k1_relat_1(X3)) | k7_relat_1(sK2,sK0) = X3) )),
% 4.52/0.96    inference(subsumption_resolution,[],[f126,f465])).
% 4.52/0.96  fof(f126,plain,(
% 4.52/0.96    ( ! [X3] : (k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(X3) | r2_hidden(sK3(X3,k7_relat_1(sK2,sK0)),k1_relat_1(X3)) | k7_relat_1(sK2,sK0) = X3) )),
% 4.52/0.96    inference(superposition,[],[f60,f117])).
% 4.52/0.96  fof(f60,plain,(
% 4.52/0.96    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 4.52/0.96    inference(cnf_transformation,[],[f34])).
% 4.52/0.96  fof(f4642,plain,(
% 4.52/0.96    k1_funct_1(sK2,sK3(sK1,k7_relat_1(sK2,sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),sK3(sK1,k7_relat_1(sK2,sK0))) | ~spl4_1),
% 4.52/0.96    inference(resolution,[],[f781,f2119])).
% 4.52/0.96  fof(f781,plain,(
% 4.52/0.96    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),X1)) )),
% 4.52/0.96    inference(forward_demodulation,[],[f757,f117])).
% 4.52/0.96  fof(f757,plain,(
% 4.52/0.96    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,sK0))) | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK2),X1)) )),
% 4.52/0.96    inference(superposition,[],[f121,f285])).
% 4.52/0.96  fof(f121,plain,(
% 4.52/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1)) )),
% 4.52/0.96    inference(subsumption_resolution,[],[f120,f49])).
% 4.52/0.96  fof(f120,plain,(
% 4.52/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | ~v1_relat_1(sK2) | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1)) )),
% 4.52/0.96    inference(subsumption_resolution,[],[f118,f50])).
% 4.52/0.96  fof(f118,plain,(
% 4.52/0.96    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1)) )),
% 4.52/0.96    inference(superposition,[],[f59,f86])).
% 4.52/0.96  fof(f59,plain,(
% 4.52/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f32])).
% 4.52/0.96  fof(f32,plain,(
% 4.52/0.96    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.52/0.96    inference(flattening,[],[f31])).
% 4.52/0.96  fof(f31,plain,(
% 4.52/0.96    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.52/0.96    inference(ennf_transformation,[],[f21])).
% 4.52/0.96  fof(f21,axiom,(
% 4.52/0.96    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 4.52/0.96  fof(f1010,plain,(
% 4.52/0.96    spl4_1),
% 4.52/0.96    inference(avatar_contradiction_clause,[],[f1009])).
% 4.52/0.96  fof(f1009,plain,(
% 4.52/0.96    $false | spl4_1),
% 4.52/0.96    inference(subsumption_resolution,[],[f1005,f49])).
% 4.52/0.96  fof(f1005,plain,(
% 4.52/0.96    ~v1_relat_1(sK2) | spl4_1),
% 4.52/0.96    inference(resolution,[],[f999,f56])).
% 4.52/0.96  fof(f56,plain,(
% 4.52/0.96    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f28])).
% 4.52/0.96  fof(f28,plain,(
% 4.52/0.96    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.52/0.96    inference(ennf_transformation,[],[f6])).
% 4.52/0.96  fof(f6,axiom,(
% 4.52/0.96    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.52/0.96  fof(f999,plain,(
% 4.52/0.96    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_1),
% 4.52/0.96    inference(avatar_component_clause,[],[f997])).
% 4.52/0.96  % SZS output end Proof for theBenchmark
% 4.52/0.96  % (6199)------------------------------
% 4.52/0.96  % (6199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.96  % (6199)Termination reason: Refutation
% 4.52/0.96  
% 4.52/0.96  % (6199)Memory used [KB]: 10362
% 4.52/0.96  % (6199)Time elapsed: 0.542 s
% 4.52/0.96  % (6199)------------------------------
% 4.52/0.96  % (6199)------------------------------
% 4.52/0.97  % (6171)Success in time 0.602 s
%------------------------------------------------------------------------------
