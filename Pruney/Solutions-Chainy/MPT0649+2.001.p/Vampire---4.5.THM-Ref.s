%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 187 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :   17
%              Number of atoms          :  257 ( 905 expanded)
%              Number of equality atoms :   76 ( 258 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f158,f110])).

fof(f110,plain,(
    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f21,f108])).

fof(f108,plain,(
    sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(resolution,[],[f107,f25])).

fof(f25,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f61,f24])).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X3] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f60,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | k1_funct_1(X1,X2) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f21,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f158,plain,(
    sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(forward_demodulation,[],[f156,f108])).

fof(f156,plain,(
    k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(resolution,[],[f154,f25])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) ) ),
    inference(forward_demodulation,[],[f153,f81])).

fof(f81,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f79,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
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

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f77,f22])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f76,f23])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f72,f27])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1))) ) ),
    inference(superposition,[],[f26,f67])).

fof(f67,plain,(
    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f66,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f65,f23])).

fof(f65,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f153,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) ) ),
    inference(subsumption_resolution,[],[f151,f22])).

fof(f151,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f149,f23])).

fof(f149,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_funct_1(k5_relat_1(sK1,k2_funct_1(X1)),X2) = k1_funct_1(k2_funct_1(X1),k1_funct_1(sK1,X2))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,k2_funct_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f147,f27])).

fof(f147,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,k2_funct_1(X1))))
      | k1_funct_1(k5_relat_1(sK1,k2_funct_1(X1)),X2) = k1_funct_1(k2_funct_1(X1),k1_funct_1(sK1,X2))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f144,f28])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,X0)))
      | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f142,f22])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,X0)))
      | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1)) ) ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (10505)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.46  % (10497)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (10505)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f21,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.48    inference(resolution,[],[f107,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.48    inference(resolution,[],[f61,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v2_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.48    inference(equality_resolution,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.48    inference(equality_resolution,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | k1_funct_1(X1,X2) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f156,f108])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.48    inference(resolution,[],[f154,f25])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f153,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f22])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))),
% 0.21/0.48    inference(resolution,[],[f78,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f22])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1))) | ~v1_relat_1(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f23])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f72,f27])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK1)) | ~r1_tarski(k2_relat_1(X0),k2_relat_1(sK1)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK1)))) )),
% 0.21/0.48    inference(superposition,[],[f26,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f22])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f23])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.48    inference(resolution,[],[f29,f24])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f22])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_relat_1(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f149,f23])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_funct_1(k5_relat_1(sK1,k2_funct_1(X1)),X2) = k1_funct_1(k2_funct_1(X1),k1_funct_1(sK1,X2)) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,k2_funct_1(X1)))) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f27])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_relat_1(k2_funct_1(X1)) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(sK1,k2_funct_1(X1)))) | k1_funct_1(k5_relat_1(sK1,k2_funct_1(X1)),X2) = k1_funct_1(k2_funct_1(X1),k1_funct_1(sK1,X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f144,f28])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,X0))) | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f22])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,X0))) | k1_funct_1(k5_relat_1(sK1,X0),X1) = k1_funct_1(X0,k1_funct_1(sK1,X1))) )),
% 0.21/0.48    inference(resolution,[],[f41,f23])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10505)------------------------------
% 0.21/0.48  % (10505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10505)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10505)Memory used [KB]: 1791
% 0.21/0.48  % (10505)Time elapsed: 0.080 s
% 0.21/0.48  % (10505)------------------------------
% 0.21/0.48  % (10505)------------------------------
% 0.21/0.48  % (10485)Success in time 0.125 s
%------------------------------------------------------------------------------
