%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0581+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 33.07s
% Output     : Refutation 33.07s
% Verified   : 
% Statistics : Number of formulae       :   22 (  57 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 269 expanded)
%              Number of equality atoms :   44 ( 179 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61049,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61048,f1243])).

fof(f1243,plain,(
    k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f1094])).

fof(f1094,plain,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f847,f1093,f1092,f1091])).

fof(f1091,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(X1,k2_xboole_0(X2,X3)) != k7_relat_1(sK0,k2_xboole_0(X2,X3))
              & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
              & k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1092,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( k7_relat_1(X1,k2_xboole_0(X2,X3)) != k7_relat_1(sK0,k2_xboole_0(X2,X3))
            & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
            & k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
        & v1_relat_1(X1) )
   => ( ? [X3,X2] :
          ( k7_relat_1(sK0,k2_xboole_0(X2,X3)) != k7_relat_1(sK1,k2_xboole_0(X2,X3))
          & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
          & k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1093,plain,
    ( ? [X3,X2] :
        ( k7_relat_1(sK0,k2_xboole_0(X2,X3)) != k7_relat_1(sK1,k2_xboole_0(X2,X3))
        & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        & k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
   => ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
      & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
      & k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f847,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f846])).

fof(f846,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f773])).

fof(f773,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
               => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f772])).

fof(f772,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
             => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_relat_1)).

fof(f61048,plain,(
    k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) = k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f60929,f1701])).

fof(f1701,plain,(
    ! [X21,X20] : k7_relat_1(sK0,k2_xboole_0(X20,X21)) = k2_xboole_0(k7_relat_1(sK0,X20),k7_relat_1(sK0,X21)) ),
    inference(resolution,[],[f1239,f1274])).

fof(f1274,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f869])).

fof(f869,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f697])).

fof(f697,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).

fof(f1239,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1094])).

fof(f60929,plain,(
    k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK0,sK3)) ),
    inference(superposition,[],[f2255,f1242])).

fof(f1242,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f1094])).

fof(f2255,plain,(
    ! [X11] : k7_relat_1(sK1,k2_xboole_0(sK2,X11)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X11)) ),
    inference(subsumption_resolution,[],[f2178,f1240])).

fof(f1240,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1094])).

fof(f2178,plain,(
    ! [X11] :
      ( k7_relat_1(sK1,k2_xboole_0(sK2,X11)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X11))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f1274,f1241])).

fof(f1241,plain,(
    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f1094])).
%------------------------------------------------------------------------------
