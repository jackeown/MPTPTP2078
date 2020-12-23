%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0595+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  67 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 327 expanded)
%              Number of equality atoms :   32 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f34])).

fof(f34,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f33,f30])).

fof(f30,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(resolution,[],[f19,f11])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2))
    & k2_relat_1(sK0) = k2_relat_1(sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
                & k2_relat_1(X0) = k2_relat_1(X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X1,X2)) != k2_relat_1(k5_relat_1(sK0,X2))
              & k2_relat_1(X1) = k2_relat_1(sK0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_relat_1(k5_relat_1(X1,X2)) != k2_relat_1(k5_relat_1(sK0,X2))
            & k2_relat_1(X1) = k2_relat_1(sK0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k2_relat_1(k5_relat_1(sK0,X2)) != k2_relat_1(k5_relat_1(sK1,X2))
          & k2_relat_1(sK0) = k2_relat_1(sK1)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( k2_relat_1(k5_relat_1(sK0,X2)) != k2_relat_1(k5_relat_1(sK1,X2))
        & k2_relat_1(sK0) = k2_relat_1(sK1)
        & v1_relat_1(X2) )
   => ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2))
      & k2_relat_1(sK0) = k2_relat_1(sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k2_relat_1(X0) = k2_relat_1(X1)
                 => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f19,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k5_relat_1(X2,sK2)) = k9_relat_1(sK2,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f16,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f33,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f31,f14])).

fof(f14,plain,(
    k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(resolution,[],[f19,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
