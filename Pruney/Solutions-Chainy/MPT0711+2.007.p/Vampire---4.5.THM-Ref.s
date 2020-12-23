%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 993 expanded)
%              Number of leaves         :   13 ( 367 expanded)
%              Depth                    :   27
%              Number of atoms          :  337 (6249 expanded)
%              Number of equality atoms :  101 (2628 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1285,plain,(
    $false ),
    inference(resolution,[],[f1281,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(f1281,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    inference(global_subsumption,[],[f37,f34,f33,f32,f31,f1280])).

fof(f1280,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f1279])).

fof(f1279,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f1278,f35])).

fof(f35,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f1278,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f1277,f190])).

fof(f190,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(backward_demodulation,[],[f175,f178])).

fof(f178,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(backward_demodulation,[],[f63,f175])).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f31,f61,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f56,f35])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f47])).

fof(f175,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f174,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f174,plain,(
    ! [X0] : k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f160,f171])).

fof(f171,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f82,f170])).

fof(f170,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) ),
    inference(forward_demodulation,[],[f169,f40])).

fof(f169,plain,(
    ! [X0] : k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) ),
    inference(forward_demodulation,[],[f161,f35])).

fof(f161,plain,(
    ! [X0] : k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f33,f38,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f82,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ),
    inference(forward_demodulation,[],[f71,f35])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) ),
    inference(unit_resulting_resolution,[],[f33,f54,f48])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(unit_resulting_resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f160,plain,(
    ! [X0] : k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f31,f38,f42])).

fof(f1277,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f1276,f189])).

fof(f189,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(backward_demodulation,[],[f172,f178])).

fof(f172,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f170,f171])).

fof(f1276,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f1275])).

fof(f1275,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f45,f983])).

fof(f983,plain,(
    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f976,f36])).

fof(f36,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f976,plain,(
    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),sK2) ),
    inference(unit_resulting_resolution,[],[f31,f964,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f964,plain,(
    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),k1_relat_1(k7_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f37,f762])).

fof(f762,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0) ) ),
    inference(global_subsumption,[],[f31,f761])).

fof(f761,plain,(
    ! [X0] :
      ( k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0)
      | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f760,f190])).

fof(f760,plain,(
    ! [X0] :
      ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
      | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f754,f189])).

fof(f754,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f628,f47])).

fof(f628,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(global_subsumption,[],[f33,f627])).

fof(f627,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | ~ v1_relat_1(sK1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(duplicate_literal_removal,[],[f626])).

fof(f626,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | ~ v1_relat_1(sK1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(forward_demodulation,[],[f623,f35])).

fof(f623,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | ~ v1_relat_1(sK1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(resolution,[],[f237,f34])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) ) ),
    inference(global_subsumption,[],[f31,f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
                    & r2_hidden(sK3(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:37:25 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.48  % (16812)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (16803)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (16826)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.49  % (16810)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (16807)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (16823)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (16808)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (16819)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (16805)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (16821)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (16825)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (16817)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (16804)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (16820)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (16824)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (16822)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (16816)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (16815)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (16809)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (16814)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (16813)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (16826)Refutation not found, incomplete strategy% (16826)------------------------------
% 0.21/0.51  % (16826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16826)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16826)Memory used [KB]: 10618
% 0.21/0.51  % (16826)Time elapsed: 0.102 s
% 0.21/0.51  % (16826)------------------------------
% 0.21/0.51  % (16826)------------------------------
% 0.21/0.51  % (16811)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (16811)Refutation not found, incomplete strategy% (16811)------------------------------
% 0.21/0.52  % (16811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16811)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16811)Memory used [KB]: 10618
% 0.21/0.52  % (16811)Time elapsed: 0.108 s
% 0.21/0.52  % (16811)------------------------------
% 0.21/0.52  % (16811)------------------------------
% 0.21/0.52  % (16806)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.53  % (16818)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.69/0.58  % (16817)Refutation found. Thanks to Tanya!
% 1.69/0.58  % SZS status Theorem for theBenchmark
% 1.69/0.58  % SZS output start Proof for theBenchmark
% 1.69/0.58  fof(f1285,plain,(
% 1.69/0.58    $false),
% 1.69/0.58    inference(resolution,[],[f1281,f55])).
% 1.69/0.58  fof(f55,plain,(
% 1.69/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK0))) )),
% 1.69/0.58    inference(unit_resulting_resolution,[],[f31,f47])).
% 1.69/0.58  fof(f47,plain,(
% 1.69/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f17])).
% 1.69/0.58  fof(f17,plain,(
% 1.69/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.69/0.58    inference(ennf_transformation,[],[f5])).
% 1.69/0.58  fof(f5,axiom,(
% 1.69/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 1.69/0.58  fof(f31,plain,(
% 1.69/0.58    v1_relat_1(sK0)),
% 1.69/0.58    inference(cnf_transformation,[],[f24])).
% 1.69/0.58  fof(f24,plain,(
% 1.69/0.58    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 1.80/0.59  fof(f21,plain,(
% 1.80/0.59    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f22,plain,(
% 1.80/0.59    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f23,plain,(
% 1.80/0.59    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f12,plain,(
% 1.80/0.59    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.80/0.59    inference(flattening,[],[f11])).
% 1.80/0.59  fof(f11,plain,(
% 1.80/0.59    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.80/0.59    inference(ennf_transformation,[],[f10])).
% 1.80/0.59  fof(f10,negated_conjecture,(
% 1.80/0.59    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.80/0.59    inference(negated_conjecture,[],[f9])).
% 1.80/0.59  fof(f9,conjecture,(
% 1.80/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 1.80/0.59  fof(f1281,plain,(
% 1.80/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 1.80/0.59    inference(global_subsumption,[],[f37,f34,f33,f32,f31,f1280])).
% 1.80/0.59  fof(f1280,plain,(
% 1.80/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.80/0.59    inference(duplicate_literal_removal,[],[f1279])).
% 1.80/0.59  fof(f1279,plain,(
% 1.80/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.80/0.59    inference(forward_demodulation,[],[f1278,f35])).
% 1.80/0.59  fof(f35,plain,(
% 1.80/0.59    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 1.80/0.59    inference(cnf_transformation,[],[f24])).
% 1.80/0.59  fof(f1278,plain,(
% 1.80/0.59    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.80/0.59    inference(forward_demodulation,[],[f1277,f190])).
% 1.80/0.59  fof(f190,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.80/0.59    inference(backward_demodulation,[],[f175,f178])).
% 1.80/0.59  fof(f178,plain,(
% 1.80/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.80/0.59    inference(backward_demodulation,[],[f63,f175])).
% 1.80/0.59  fof(f63,plain,(
% 1.80/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X0))))) )),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f31,f61,f48])).
% 1.80/0.59  fof(f48,plain,(
% 1.80/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f19])).
% 1.80/0.59  fof(f19,plain,(
% 1.80/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.80/0.59    inference(flattening,[],[f18])).
% 1.80/0.59  fof(f18,plain,(
% 1.80/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.80/0.59    inference(ennf_transformation,[],[f6])).
% 1.80/0.59  fof(f6,axiom,(
% 1.80/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.80/0.59  fof(f61,plain,(
% 1.80/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f56,f35])).
% 1.80/0.59  fof(f56,plain,(
% 1.80/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) )),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f33,f47])).
% 1.80/0.59  fof(f175,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f174,f40])).
% 1.80/0.59  fof(f40,plain,(
% 1.80/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f2])).
% 1.80/0.59  fof(f2,axiom,(
% 1.80/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.80/0.59  fof(f174,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f160,f171])).
% 1.80/0.59  fof(f171,plain,(
% 1.80/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))) )),
% 1.80/0.59    inference(backward_demodulation,[],[f82,f170])).
% 1.80/0.59  fof(f170,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f169,f40])).
% 1.80/0.59  fof(f169,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f161,f35])).
% 1.80/0.59  fof(f161,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) )),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f33,f38,f42])).
% 1.80/0.59  fof(f42,plain,(
% 1.80/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f13])).
% 1.80/0.59  fof(f13,plain,(
% 1.80/0.59    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.80/0.59    inference(ennf_transformation,[],[f1])).
% 1.80/0.59  fof(f1,axiom,(
% 1.80/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 1.80/0.59  fof(f38,plain,(
% 1.80/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f7])).
% 1.80/0.59  fof(f7,axiom,(
% 1.80/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.80/0.59  fof(f82,plain,(
% 1.80/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0)))))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f71,f35])).
% 1.80/0.59  fof(f71,plain,(
% 1.80/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))))) )),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f33,f54,f48])).
% 1.80/0.59  fof(f54,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f38,f46])).
% 1.80/0.59  fof(f46,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f16])).
% 1.80/0.59  fof(f16,plain,(
% 1.80/0.59    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.80/0.59    inference(ennf_transformation,[],[f4])).
% 1.80/0.59  fof(f4,axiom,(
% 1.80/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.80/0.59  fof(f160,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) )),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f31,f38,f42])).
% 1.80/0.59  fof(f1277,plain,(
% 1.80/0.59    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.80/0.59    inference(forward_demodulation,[],[f1276,f189])).
% 1.80/0.59  fof(f189,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.80/0.59    inference(backward_demodulation,[],[f172,f178])).
% 1.80/0.59  fof(f172,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.80/0.59    inference(backward_demodulation,[],[f170,f171])).
% 1.80/0.59  fof(f1276,plain,(
% 1.80/0.59    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.80/0.59    inference(trivial_inequality_removal,[],[f1275])).
% 1.80/0.59  fof(f1275,plain,(
% 1.80/0.59    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.80/0.59    inference(superposition,[],[f45,f983])).
% 1.80/0.59  fof(f983,plain,(
% 1.80/0.59    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f976,f36])).
% 1.80/0.59  fof(f36,plain,(
% 1.80/0.59    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f24])).
% 1.80/0.59  fof(f976,plain,(
% 1.80/0.59    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),sK2)),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f31,f964,f49])).
% 1.80/0.59  fof(f49,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f30])).
% 1.80/0.59  fof(f30,plain,(
% 1.80/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.80/0.59    inference(flattening,[],[f29])).
% 1.80/0.59  fof(f29,plain,(
% 1.80/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.80/0.59    inference(nnf_transformation,[],[f20])).
% 1.80/0.59  fof(f20,plain,(
% 1.80/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.80/0.59    inference(ennf_transformation,[],[f3])).
% 1.80/0.59  fof(f3,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 1.80/0.59  fof(f964,plain,(
% 1.80/0.59    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),k1_relat_1(k7_relat_1(sK0,sK2)))),
% 1.80/0.59    inference(unit_resulting_resolution,[],[f37,f762])).
% 1.80/0.59  fof(f762,plain,(
% 1.80/0.59    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0)) )),
% 1.80/0.59    inference(global_subsumption,[],[f31,f761])).
% 1.80/0.59  fof(f761,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f760,f190])).
% 1.80/0.59  fof(f760,plain,(
% 1.80/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f754,f189])).
% 1.80/0.59  fof(f754,plain,(
% 1.80/0.59    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.80/0.59    inference(resolution,[],[f628,f47])).
% 1.80/0.59  fof(f628,plain,(
% 1.80/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.80/0.59    inference(global_subsumption,[],[f33,f627])).
% 1.80/0.59  fof(f627,plain,(
% 1.80/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~v1_relat_1(sK1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.80/0.59    inference(duplicate_literal_removal,[],[f626])).
% 1.80/0.59  fof(f626,plain,(
% 1.80/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~v1_relat_1(sK1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f623,f35])).
% 1.80/0.59  fof(f623,plain,(
% 1.80/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~v1_relat_1(sK1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.80/0.59    inference(resolution,[],[f237,f34])).
% 1.80/0.59  fof(f237,plain,(
% 1.80/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,X0,X1),X1) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)) )),
% 1.80/0.59    inference(global_subsumption,[],[f31,f234])).
% 1.80/0.59  fof(f234,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(sK0)) )),
% 1.80/0.59    inference(resolution,[],[f44,f32])).
% 1.80/0.59  fof(f44,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f28])).
% 1.80/0.59  fof(f28,plain,(
% 1.80/0.59    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.80/0.59  fof(f27,plain,(
% 1.80/0.59    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f26,plain,(
% 1.80/0.59    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.59    inference(rectify,[],[f25])).
% 1.80/0.59  fof(f25,plain,(
% 1.80/0.59    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.59    inference(nnf_transformation,[],[f15])).
% 1.80/0.59  fof(f15,plain,(
% 1.80/0.59    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.80/0.59    inference(flattening,[],[f14])).
% 1.80/0.59  fof(f14,plain,(
% 1.80/0.59    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.80/0.59    inference(ennf_transformation,[],[f8])).
% 1.80/0.59  fof(f8,axiom,(
% 1.80/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 1.80/0.59  fof(f45,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f28])).
% 1.80/0.59  fof(f32,plain,(
% 1.80/0.59    v1_funct_1(sK0)),
% 1.80/0.59    inference(cnf_transformation,[],[f24])).
% 1.80/0.59  fof(f33,plain,(
% 1.80/0.59    v1_relat_1(sK1)),
% 1.80/0.59    inference(cnf_transformation,[],[f24])).
% 1.80/0.59  fof(f34,plain,(
% 1.80/0.59    v1_funct_1(sK1)),
% 1.80/0.59    inference(cnf_transformation,[],[f24])).
% 1.80/0.59  fof(f37,plain,(
% 1.80/0.59    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f24])).
% 1.80/0.59  % SZS output end Proof for theBenchmark
% 1.80/0.59  % (16817)------------------------------
% 1.80/0.59  % (16817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.59  % (16817)Termination reason: Refutation
% 1.80/0.59  
% 1.80/0.59  % (16817)Memory used [KB]: 11641
% 1.80/0.59  % (16817)Time elapsed: 0.110 s
% 1.80/0.59  % (16817)------------------------------
% 1.80/0.59  % (16817)------------------------------
% 1.80/0.59  % (16799)Success in time 0.233 s
%------------------------------------------------------------------------------
