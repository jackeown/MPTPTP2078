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
% DateTime   : Thu Dec  3 12:52:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 277 expanded)
%              Number of leaves         :   10 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  415 (1681 expanded)
%              Number of equality atoms :  139 ( 539 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(subsumption_resolution,[],[f242,f160])).

fof(f160,plain,(
    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(subsumption_resolution,[],[f36,f157])).

fof(f157,plain,(
    sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(resolution,[],[f156,f35])).

fof(f35,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
      | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
    & r2_hidden(sK0,k2_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
        | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
      & r2_hidden(sK0,k2_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f156,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f155,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f154,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f74,f34])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X4,X0] :
      ( ~ v2_funct_1(X0)
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f70,plain,(
    ! [X4,X0] :
      ( k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f64,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X4,X0] :
      ( k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( k1_funct_1(X0,k1_funct_1(X1,X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X0,X5) = X4
      | k1_funct_1(X1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
                  | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
                & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
              | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
                  | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            | ~ r2_hidden(sK2(X0,X1),k2_relat_1(X0)) )
          & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
        | ( ( sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
            | ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f36,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f242,plain,(
    sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(forward_demodulation,[],[f239,f157])).

fof(f239,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(resolution,[],[f237,f35])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) ) ),
    inference(forward_demodulation,[],[f236,f128])).

fof(f128,plain,(
    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) ),
    inference(subsumption_resolution,[],[f126,f32])).

fof(f126,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f124,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f58,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f123,f101])).

fof(f101,plain,(
    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f100,f32])).

fof(f100,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f99,f33])).

fof(f99,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f53,f34])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_relat_1(k2_funct_1(sK1)) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f121,f78])).

fof(f78,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f55,f33])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_relat_1(k2_funct_1(sK1)) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK1)) ) ),
    inference(superposition,[],[f38,f104])).

fof(f104,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f103,f32])).

fof(f103,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f102,f33])).

fof(f102,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f54,f34])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

% (24384)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
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

fof(f236,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) ) ),
    inference(subsumption_resolution,[],[f234,f32])).

fof(f234,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f232,f33])).

fof(f232,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_funct_1(k5_relat_1(k2_funct_1(X2),sK1),X1) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X2),X1))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k2_funct_1(X2),sK1)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f230,f55])).

fof(f230,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k2_funct_1(X2),sK1)))
      | ~ v1_relat_1(k2_funct_1(X2))
      | k1_funct_1(k5_relat_1(k2_funct_1(X2),sK1),X1) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f227,f56])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1)))
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f225,f32])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:53:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (24369)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.48  % (24377)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (24377)Refutation not found, incomplete strategy% (24377)------------------------------
% 0.20/0.49  % (24377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24377)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (24377)Memory used [KB]: 10618
% 0.20/0.49  % (24377)Time elapsed: 0.094 s
% 0.20/0.49  % (24377)------------------------------
% 0.20/0.49  % (24377)------------------------------
% 0.20/0.51  % (24382)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (24364)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (24365)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (24370)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (24371)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (24385)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (24374)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (24372)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24360)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (24361)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (24366)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (24380)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (24376)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (24362)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (24388)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (24389)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (24382)Refutation not found, incomplete strategy% (24382)------------------------------
% 0.20/0.53  % (24382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24382)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24382)Memory used [KB]: 10874
% 0.20/0.53  % (24382)Time elapsed: 0.095 s
% 0.20/0.53  % (24382)------------------------------
% 0.20/0.53  % (24382)------------------------------
% 0.20/0.53  % (24363)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (24362)Refutation not found, incomplete strategy% (24362)------------------------------
% 0.20/0.53  % (24362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24362)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24362)Memory used [KB]: 10746
% 0.20/0.53  % (24362)Time elapsed: 0.129 s
% 0.20/0.53  % (24362)------------------------------
% 0.20/0.53  % (24362)------------------------------
% 0.20/0.53  % (24375)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (24383)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (24365)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f243,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f242,f160])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f36,f157])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.20/0.54    inference(resolution,[],[f156,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    (sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f7])).
% 0.20/0.54  fof(f7,conjecture,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f155,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    v1_relat_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = X0 | ~v1_relat_1(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f154,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    v1_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f74,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    v2_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X4,X0] : (~v2_funct_1(X0) | ~r2_hidden(X4,k2_relat_1(X0)) | k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f70,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X4,X0] : (k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4 | ~r2_hidden(X4,k2_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f64,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X4,X0] : (k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4 | ~r2_hidden(X4,k2_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X4,X0,X1] : (k1_funct_1(X0,k1_funct_1(X1,X4)) = X4 | ~r2_hidden(X4,k2_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X4,X0,X5,X1] : (k1_funct_1(X0,X5) = X4 | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) => (((sK3(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | ~r2_hidden(sK2(X0,X1),k2_relat_1(X0))) & sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | ((sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),k1_relat_1(X0))) & sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k2_relat_1(X0)))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & ((k1_funct_1(X0,X5) = X4 & r2_hidden(X5,k1_relat_1(X0))) | k1_funct_1(X1,X4) != X5 | ~r2_hidden(X4,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(rectify,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) | k2_relat_1(X0) != k1_relat_1(X1))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f242,plain,(
% 0.20/0.54    sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f239,f157])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.20/0.54    inference(resolution,[],[f237,f35])).
% 0.20/0.54  fof(f237,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f236,f128])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f126,f32])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.54    inference(resolution,[],[f124,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f58,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f123,f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f100,f32])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f99,f33])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.54    inference(resolution,[],[f53,f34])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_relat_1(k2_funct_1(sK1)) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f121,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f77,f32])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.54    inference(resolution,[],[f55,f33])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_relat_1(k2_funct_1(sK1)) = k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK1))) )),
% 0.20/0.54    inference(superposition,[],[f38,f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f103,f32])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f102,f33])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.54    inference(resolution,[],[f54,f34])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  % (24384)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.54  fof(f236,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f234,f32])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X0)) = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) | ~v1_relat_1(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f232,f33])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_funct_1(k5_relat_1(k2_funct_1(X2),sK1),X1) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X2),X1)) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(k2_funct_1(X2),sK1))) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f230,f55])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(k2_funct_1(X2),sK1))) | ~v1_relat_1(k2_funct_1(X2)) | k1_funct_1(k5_relat_1(k2_funct_1(X2),sK1),X1) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(resolution,[],[f227,f56])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1))) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f225,f32])).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f37,f33])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (24365)------------------------------
% 0.20/0.54  % (24365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24365)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (24365)Memory used [KB]: 6524
% 0.20/0.54  % (24365)Time elapsed: 0.122 s
% 0.20/0.54  % (24365)------------------------------
% 0.20/0.54  % (24365)------------------------------
% 0.20/0.54  % (24359)Success in time 0.187 s
%------------------------------------------------------------------------------
