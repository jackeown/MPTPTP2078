%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:59 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 850 expanded)
%              Number of leaves         :   10 ( 244 expanded)
%              Depth                    :   24
%              Number of atoms          :  407 (9998 expanded)
%              Number of equality atoms :  156 (4687 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f486,f65])).

fof(f65,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f37,f64])).

fof(f64,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_funct_1(sK0) != sK1
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK0,X2) = X3
            | k1_funct_1(sK1,X3) != X2 )
          & ( k1_funct_1(sK1,X3) = X2
            | k1_funct_1(sK0,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & ! [X2,X3] :
                ( ( ( k1_funct_1(X0,X2) = X3
                    | k1_funct_1(X1,X3) != X2 )
                  & ( k1_funct_1(X1,X3) = X2
                    | k1_funct_1(X0,X2) != X3 ) )
                | ~ r2_hidden(X3,k1_relat_1(X1))
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k2_relat_1(X0) = k1_relat_1(X1)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & ! [X3,X2] :
            ( ( ( k1_funct_1(sK0,X2) = X3
                | k1_funct_1(X1,X3) != X2 )
              & ( k1_funct_1(X1,X3) = X2
                | k1_funct_1(sK0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(X1))
            | ~ r2_hidden(X2,k1_relat_1(sK0)) )
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & ! [X3,X2] :
          ( ( ( k1_funct_1(sK0,X2) = X3
              | k1_funct_1(sK1,X3) != X2 )
            & ( k1_funct_1(sK1,X3) = X2
              | k1_funct_1(sK0,X2) != X3 ) )
          | ~ r2_hidden(X3,k1_relat_1(sK1))
          | ~ r2_hidden(X2,k1_relat_1(sK0)) )
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

fof(f63,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f37,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f486,plain,(
    sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f485,f71])).

fof(f71,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f70,f28])).

fof(f70,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f40,f64])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f485,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f484,f69])).

fof(f69,plain,(
    v1_funct_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f68,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f41,f64])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f484,plain,
    ( ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f483,f54])).

fof(f54,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f483,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f481])).

fof(f481,plain,
    ( k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0)))
    | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(superposition,[],[f386,f277])).

fof(f277,plain,(
    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f274,f270])).

fof(f270,plain,(
    sK2(sK1,k4_relat_1(sK0)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0)))) ),
    inference(resolution,[],[f266,f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f154,f34])).

fof(f34,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f153,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f152,f31])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f52,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
      | ~ r2_hidden(X3,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(backward_demodulation,[],[f51,f33])).

fof(f33,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3
      | ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0)) ) ),
    inference(backward_demodulation,[],[f48,f34])).

fof(f48,plain,(
    ! [X3] :
      ( k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK0,X2) = X3
      | k1_funct_1(sK1,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f266,plain,(
    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f265,f65])).

fof(f265,plain,
    ( r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f264,f71])).

fof(f264,plain,
    ( r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f260,f54])).

fof(f260,plain,
    ( r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(resolution,[],[f253,f69])).

fof(f253,plain,(
    ! [X4] :
      ( ~ v1_funct_1(X4)
      | r2_hidden(sK2(sK1,X4),k2_relat_1(sK0))
      | k2_relat_1(sK0) != k1_relat_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4 ) ),
    inference(forward_demodulation,[],[f252,f34])).

fof(f252,plain,(
    ! [X4] :
      ( r2_hidden(sK2(sK1,X4),k2_relat_1(sK0))
      | k1_relat_1(sK1) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4 ) ),
    inference(forward_demodulation,[],[f251,f34])).

fof(f251,plain,(
    ! [X4] :
      ( r2_hidden(sK2(sK1,X4),k1_relat_1(sK1))
      | k1_relat_1(sK1) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4 ) ),
    inference(subsumption_resolution,[],[f243,f30])).

fof(f243,plain,(
    ! [X4] :
      ( r2_hidden(sK2(sK1,X4),k1_relat_1(sK1))
      | k1_relat_1(sK1) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f274,plain,(
    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))))) ),
    inference(resolution,[],[f266,f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0))) ) ),
    inference(forward_demodulation,[],[f192,f34])).

fof(f192,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0)))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f191,f30])).

fof(f191,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f189,f31])).

fof(f189,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f188,f45])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f187,f64])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f186,f33])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f185,f28])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f29])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f386,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK2(sK1,X4)) != k1_funct_1(X4,sK2(sK1,X4))
      | k2_relat_1(sK0) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4 ) ),
    inference(forward_demodulation,[],[f385,f34])).

fof(f385,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK2(sK1,X4)) != k1_funct_1(X4,sK2(sK1,X4))
      | k1_relat_1(sK1) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4 ) ),
    inference(subsumption_resolution,[],[f379,f30])).

fof(f379,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK2(sK1,X4)) != k1_funct_1(X4,sK2(sK1,X4))
      | k1_relat_1(sK1) != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | sK1 = X4
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f44,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (22990)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (23007)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (22997)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (22991)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.45/0.55  % (23006)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.45/0.55  % (22988)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.45/0.55  % (22996)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.45/0.55  % (22986)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.45/0.55  % (23005)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.45/0.56  % (22989)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.45/0.56  % (22999)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.45/0.56  % (22994)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.45/0.56  % (22998)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.45/0.56  % (23001)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.53/0.56  % (22985)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.53/0.56  % (22987)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.53/0.56  % (23004)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.53/0.56  % (22995)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.53/0.56  % (23008)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.53/0.57  % (22983)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.53/0.57  % (23000)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.53/0.57  % (22992)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.53/0.58  % (22984)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.58  % (22986)Refutation found. Thanks to Tanya!
% 1.53/0.58  % SZS status Theorem for theBenchmark
% 1.53/0.58  % (23003)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.53/0.58  % (23002)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.53/0.59  % (22993)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.53/0.60  % SZS output start Proof for theBenchmark
% 1.53/0.60  fof(f487,plain,(
% 1.53/0.60    $false),
% 1.53/0.60    inference(subsumption_resolution,[],[f486,f65])).
% 1.53/0.60  fof(f65,plain,(
% 1.53/0.60    sK1 != k4_relat_1(sK0)),
% 1.53/0.60    inference(superposition,[],[f37,f64])).
% 1.53/0.60  fof(f64,plain,(
% 1.53/0.60    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f63,f28])).
% 1.53/0.60  fof(f28,plain,(
% 1.53/0.60    v1_relat_1(sK0)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f25,plain,(
% 1.53/0.60    (k2_funct_1(sK0) != sK1 & ! [X2,X3] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2) & (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k2_relat_1(sK0) = k1_relat_1(sK1) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.53/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 1.53/0.60  fof(f23,plain,(
% 1.53/0.60    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k2_relat_1(sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f24,plain,(
% 1.53/0.60    ? [X1] : (k2_funct_1(sK0) != X1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k2_relat_1(sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2) & (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k2_relat_1(sK0) = k1_relat_1(sK1) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f22,plain,(
% 1.53/0.60    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.53/0.60    inference(nnf_transformation,[],[f10])).
% 1.53/0.60  fof(f10,plain,(
% 1.53/0.60    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.53/0.60    inference(flattening,[],[f9])).
% 1.53/0.60  fof(f9,plain,(
% 1.53/0.60    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f8])).
% 1.53/0.60  fof(f8,negated_conjecture,(
% 1.53/0.60    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.53/0.60    inference(negated_conjecture,[],[f7])).
% 1.53/0.60  fof(f7,conjecture,(
% 1.53/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).
% 1.53/0.60  fof(f63,plain,(
% 1.53/0.60    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f62,f29])).
% 1.53/0.60  fof(f29,plain,(
% 1.53/0.60    v1_funct_1(sK0)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f62,plain,(
% 1.53/0.60    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.53/0.60    inference(resolution,[],[f42,f32])).
% 1.53/0.60  fof(f32,plain,(
% 1.53/0.60    v2_funct_1(sK0)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f42,plain,(
% 1.53/0.60    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f15])).
% 1.53/0.60  fof(f15,plain,(
% 1.53/0.60    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.60    inference(flattening,[],[f14])).
% 1.53/0.60  fof(f14,plain,(
% 1.53/0.60    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f2])).
% 1.53/0.60  fof(f2,axiom,(
% 1.53/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.53/0.60  fof(f37,plain,(
% 1.53/0.60    k2_funct_1(sK0) != sK1),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f486,plain,(
% 1.53/0.60    sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f485,f71])).
% 1.53/0.60  fof(f71,plain,(
% 1.53/0.60    v1_relat_1(k4_relat_1(sK0))),
% 1.53/0.60    inference(subsumption_resolution,[],[f70,f28])).
% 1.53/0.60  fof(f70,plain,(
% 1.53/0.60    v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f67,f29])).
% 1.53/0.60  fof(f67,plain,(
% 1.53/0.60    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.53/0.60    inference(superposition,[],[f40,f64])).
% 1.53/0.60  fof(f40,plain,(
% 1.53/0.60    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f13])).
% 1.53/0.60  fof(f13,plain,(
% 1.53/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.60    inference(flattening,[],[f12])).
% 1.53/0.60  fof(f12,plain,(
% 1.53/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f3])).
% 1.53/0.60  fof(f3,axiom,(
% 1.53/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.53/0.60  fof(f485,plain,(
% 1.53/0.60    ~v1_relat_1(k4_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f484,f69])).
% 1.53/0.60  fof(f69,plain,(
% 1.53/0.60    v1_funct_1(k4_relat_1(sK0))),
% 1.53/0.60    inference(subsumption_resolution,[],[f68,f28])).
% 1.53/0.60  fof(f68,plain,(
% 1.53/0.60    v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f66,f29])).
% 1.53/0.60  fof(f66,plain,(
% 1.53/0.60    v1_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.53/0.60    inference(superposition,[],[f41,f64])).
% 1.53/0.60  fof(f41,plain,(
% 1.53/0.60    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f13])).
% 1.53/0.60  fof(f484,plain,(
% 1.53/0.60    ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f483,f54])).
% 1.53/0.60  fof(f54,plain,(
% 1.53/0.60    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 1.53/0.60    inference(resolution,[],[f38,f28])).
% 1.53/0.60  fof(f38,plain,(
% 1.53/0.60    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f11])).
% 1.53/0.60  fof(f11,plain,(
% 1.53/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.53/0.60    inference(ennf_transformation,[],[f1])).
% 1.53/0.60  fof(f1,axiom,(
% 1.53/0.60    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.53/0.60  fof(f483,plain,(
% 1.53/0.60    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(trivial_inequality_removal,[],[f481])).
% 1.53/0.60  fof(f481,plain,(
% 1.53/0.60    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(superposition,[],[f386,f277])).
% 1.53/0.60  fof(f277,plain,(
% 1.53/0.60    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0)))),
% 1.53/0.60    inference(forward_demodulation,[],[f274,f270])).
% 1.53/0.60  fof(f270,plain,(
% 1.53/0.60    sK2(sK1,k4_relat_1(sK0)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))))),
% 1.53/0.60    inference(resolution,[],[f266,f156])).
% 1.53/0.60  fof(f156,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0) )),
% 1.53/0.60    inference(duplicate_literal_removal,[],[f155])).
% 1.53/0.60  fof(f155,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | ~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0) )),
% 1.53/0.60    inference(forward_demodulation,[],[f154,f34])).
% 1.53/0.60  fof(f34,plain,(
% 1.53/0.60    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f154,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f153,f30])).
% 1.53/0.60  fof(f30,plain,(
% 1.53/0.60    v1_relat_1(sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f153,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f152,f31])).
% 1.53/0.60  fof(f31,plain,(
% 1.53/0.60    v1_funct_1(sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f152,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.53/0.60    inference(resolution,[],[f52,f45])).
% 1.53/0.60  fof(f45,plain,(
% 1.53/0.60    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f19])).
% 1.53/0.60  fof(f19,plain,(
% 1.53/0.60    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.53/0.60    inference(flattening,[],[f18])).
% 1.53/0.60  fof(f18,plain,(
% 1.53/0.60    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.53/0.60    inference(ennf_transformation,[],[f4])).
% 1.53/0.60  fof(f4,axiom,(
% 1.53/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.53/0.60  fof(f52,plain,(
% 1.53/0.60    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | ~r2_hidden(X3,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 1.53/0.60    inference(backward_demodulation,[],[f51,f33])).
% 1.53/0.60  fof(f33,plain,(
% 1.53/0.60    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f51,plain,(
% 1.53/0.60    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 | ~r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))) )),
% 1.53/0.60    inference(backward_demodulation,[],[f48,f34])).
% 1.53/0.60  fof(f48,plain,(
% 1.53/0.60    ( ! [X3] : (k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))) )),
% 1.53/0.60    inference(equality_resolution,[],[f36])).
% 1.53/0.60  fof(f36,plain,(
% 1.53/0.60    ( ! [X2,X3] : (k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) )),
% 1.53/0.60    inference(cnf_transformation,[],[f25])).
% 1.53/0.60  fof(f266,plain,(
% 1.53/0.60    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))),
% 1.53/0.60    inference(subsumption_resolution,[],[f265,f65])).
% 1.53/0.60  fof(f265,plain,(
% 1.53/0.60    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f264,f71])).
% 1.53/0.60  fof(f264,plain,(
% 1.53/0.60    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(subsumption_resolution,[],[f260,f54])).
% 1.53/0.60  fof(f260,plain,(
% 1.53/0.60    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 1.53/0.60    inference(resolution,[],[f253,f69])).
% 1.53/0.60  fof(f253,plain,(
% 1.53/0.60    ( ! [X4] : (~v1_funct_1(X4) | r2_hidden(sK2(sK1,X4),k2_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(X4) | ~v1_relat_1(X4) | sK1 = X4) )),
% 1.53/0.60    inference(forward_demodulation,[],[f252,f34])).
% 1.53/0.60  fof(f252,plain,(
% 1.53/0.60    ( ! [X4] : (r2_hidden(sK2(sK1,X4),k2_relat_1(sK0)) | k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | sK1 = X4) )),
% 1.53/0.60    inference(forward_demodulation,[],[f251,f34])).
% 1.53/0.60  fof(f251,plain,(
% 1.53/0.60    ( ! [X4] : (r2_hidden(sK2(sK1,X4),k1_relat_1(sK1)) | k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | sK1 = X4) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f243,f30])).
% 1.53/0.60  fof(f243,plain,(
% 1.53/0.60    ( ! [X4] : (r2_hidden(sK2(sK1,X4),k1_relat_1(sK1)) | k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | sK1 = X4 | ~v1_relat_1(sK1)) )),
% 1.53/0.60    inference(resolution,[],[f43,f31])).
% 1.53/0.60  fof(f43,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f27])).
% 1.53/0.60  fof(f27,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f26])).
% 1.53/0.60  fof(f26,plain,(
% 1.53/0.60    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 1.53/0.60    introduced(choice_axiom,[])).
% 1.53/0.60  fof(f17,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.60    inference(flattening,[],[f16])).
% 1.53/0.60  fof(f16,plain,(
% 1.53/0.60    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.60    inference(ennf_transformation,[],[f6])).
% 1.53/0.60  fof(f6,axiom,(
% 1.53/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.53/0.60  fof(f274,plain,(
% 1.53/0.60    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0)))))),
% 1.53/0.60    inference(resolution,[],[f266,f193])).
% 1.53/0.60  fof(f193,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0)))) )),
% 1.53/0.60    inference(forward_demodulation,[],[f192,f34])).
% 1.53/0.60  fof(f192,plain,(
% 1.53/0.60    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0))) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f191,f30])).
% 1.53/0.60  fof(f191,plain,(
% 1.53/0.60    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0))) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f189,f31])).
% 1.53/0.60  fof(f189,plain,(
% 1.53/0.60    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X0))) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.53/0.60    inference(resolution,[],[f188,f45])).
% 1.53/0.60  fof(f188,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,X0)) = X0) )),
% 1.53/0.60    inference(forward_demodulation,[],[f187,f64])).
% 1.53/0.60  fof(f187,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0) )),
% 1.53/0.60    inference(forward_demodulation,[],[f186,f33])).
% 1.53/0.60  fof(f186,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f185,f28])).
% 1.53/0.60  fof(f185,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 | ~v1_relat_1(sK0)) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f184,f29])).
% 1.53/0.60  fof(f184,plain,(
% 1.53/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X0)) = X0 | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 1.53/0.60    inference(resolution,[],[f46,f32])).
% 1.53/0.60  fof(f46,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~v2_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f21])).
% 1.53/0.60  fof(f21,plain,(
% 1.53/0.60    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.53/0.60    inference(flattening,[],[f20])).
% 1.53/0.60  fof(f20,plain,(
% 1.53/0.60    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.53/0.60    inference(ennf_transformation,[],[f5])).
% 1.53/0.60  fof(f5,axiom,(
% 1.53/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.53/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 1.53/0.60  fof(f386,plain,(
% 1.53/0.60    ( ! [X4] : (k1_funct_1(sK1,sK2(sK1,X4)) != k1_funct_1(X4,sK2(sK1,X4)) | k2_relat_1(sK0) != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | sK1 = X4) )),
% 1.53/0.60    inference(forward_demodulation,[],[f385,f34])).
% 1.53/0.60  fof(f385,plain,(
% 1.53/0.60    ( ! [X4] : (k1_funct_1(sK1,sK2(sK1,X4)) != k1_funct_1(X4,sK2(sK1,X4)) | k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | sK1 = X4) )),
% 1.53/0.60    inference(subsumption_resolution,[],[f379,f30])).
% 1.53/0.60  fof(f379,plain,(
% 1.53/0.60    ( ! [X4] : (k1_funct_1(sK1,sK2(sK1,X4)) != k1_funct_1(X4,sK2(sK1,X4)) | k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | sK1 = X4 | ~v1_relat_1(sK1)) )),
% 1.53/0.60    inference(resolution,[],[f44,f31])).
% 1.53/0.60  fof(f44,plain,(
% 1.53/0.60    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.53/0.60    inference(cnf_transformation,[],[f27])).
% 1.53/0.60  % SZS output end Proof for theBenchmark
% 1.53/0.60  % (22986)------------------------------
% 1.53/0.60  % (22986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (22986)Termination reason: Refutation
% 1.53/0.60  
% 1.53/0.60  % (22986)Memory used [KB]: 6524
% 1.53/0.60  % (22986)Time elapsed: 0.149 s
% 1.53/0.60  % (22986)------------------------------
% 1.53/0.60  % (22986)------------------------------
% 1.53/0.60  % (22982)Success in time 0.235 s
%------------------------------------------------------------------------------
