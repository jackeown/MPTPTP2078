%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0595+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 4.68s
% Output     : Refutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   21 (  65 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 323 expanded)
%              Number of equality atoms :   31 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10299,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10298,f1513])).

fof(f1513,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f1272])).

fof(f1272,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2))
    & k2_relat_1(sK0) = k2_relat_1(sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f863,f1271,f1270,f1269])).

fof(f1269,plain,
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

fof(f1270,plain,
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

fof(f1271,plain,
    ( ? [X2] :
        ( k2_relat_1(k5_relat_1(sK0,X2)) != k2_relat_1(k5_relat_1(sK1,X2))
        & k2_relat_1(sK0) = k2_relat_1(sK1)
        & v1_relat_1(X2) )
   => ( k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2))
      & k2_relat_1(sK0) = k2_relat_1(sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f863,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f862])).

fof(f862,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f790])).

fof(f790,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k2_relat_1(X0) = k2_relat_1(X1)
                 => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f789])).

fof(f789,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f10298,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f10297,f8717])).

fof(f8717,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1509,f1511,f1544])).

fof(f1544,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f897])).

fof(f897,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f751,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1511,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1272])).

fof(f1509,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1272])).

fof(f10297,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f8718,f1512])).

fof(f1512,plain,(
    k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1272])).

fof(f8718,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1510,f1511,f1544])).

fof(f1510,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1272])).
%------------------------------------------------------------------------------
