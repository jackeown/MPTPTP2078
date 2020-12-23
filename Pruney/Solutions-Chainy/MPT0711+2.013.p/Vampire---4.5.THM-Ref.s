%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 321 expanded)
%              Number of leaves         :   10 ( 119 expanded)
%              Depth                    :   27
%              Number of atoms          :  305 (2341 expanded)
%              Number of equality atoms :   89 ( 964 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(resolution,[],[f169,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f18,plain,
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f169,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    inference(global_subsumption,[],[f32,f29,f28,f27,f26,f168])).

fof(f168,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f166,f30])).

fof(f30,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f166,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f165,f66])).

fof(f66,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f60,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    inference(unit_resulting_resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f60,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0)) ),
    inference(unit_resulting_resolution,[],[f26,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f165,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f164,f65])).

fof(f65,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f64,f46])).

fof(f64,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK0),X0)) ),
    inference(forward_demodulation,[],[f61,f30])).

fof(f61,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f28,f38])).

fof(f164,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f35,f122])).

fof(f122,plain,(
    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f116,f31])).

fof(f31,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,(
    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),sK2) ),
    inference(unit_resulting_resolution,[],[f26,f105,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f105,plain,(
    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),k1_relat_1(k7_relat_1(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f32,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0) ) ),
    inference(global_subsumption,[],[f26,f101])).

fof(f101,plain,(
    ! [X0] :
      ( k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0)
      | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f100,f65])).

fof(f100,plain,(
    ! [X0] :
      ( k7_relat_1(sK0,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
      | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f98,f66])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
      | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f97,f36])).

fof(f97,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(global_subsumption,[],[f28,f96])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | ~ v1_relat_1(sK1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | ~ v1_relat_1(sK1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(forward_demodulation,[],[f93,f30])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,sK1,X1),X1)
      | ~ v1_relat_1(sK1)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    inference(resolution,[],[f89,f29])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) ) ),
    inference(global_subsumption,[],[f26,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (19609)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (19607)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (19605)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (19606)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (19608)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (19613)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (19610)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (19626)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (19624)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (19617)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (19627)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (19623)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (19621)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (19618)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (19619)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.23/0.51  % (19616)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.23/0.51  % (19625)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.23/0.51  % (19611)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.23/0.52  % (19622)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.23/0.52  % (19620)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.23/0.52  % (19615)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.23/0.52  % (19613)Refutation not found, incomplete strategy% (19613)------------------------------
% 1.23/0.52  % (19613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (19613)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (19613)Memory used [KB]: 10618
% 1.23/0.52  % (19613)Time elapsed: 0.104 s
% 1.23/0.52  % (19613)------------------------------
% 1.23/0.52  % (19613)------------------------------
% 1.23/0.52  % (19619)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  fof(f173,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(resolution,[],[f169,f42])).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X0)),k1_relat_1(sK0))) )),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f26,f36])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f12])).
% 1.23/0.52  fof(f12,plain,(
% 1.23/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    v1_relat_1(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f9,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.23/0.52    inference(flattening,[],[f8])).
% 1.23/0.52  fof(f8,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,negated_conjecture,(
% 1.23/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.23/0.52    inference(negated_conjecture,[],[f6])).
% 1.23/0.52  fof(f6,conjecture,(
% 1.23/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 1.23/0.52  fof(f169,plain,(
% 1.23/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 1.23/0.52    inference(global_subsumption,[],[f32,f29,f28,f27,f26,f168])).
% 1.23/0.52  fof(f168,plain,(
% 1.23/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f167])).
% 1.23/0.52  fof(f167,plain,(
% 1.23/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.23/0.52    inference(forward_demodulation,[],[f166,f30])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f166,plain,(
% 1.23/0.52    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.23/0.52    inference(forward_demodulation,[],[f165,f66])).
% 1.23/0.52  fof(f66,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f60,f46])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) )),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f26,f37])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f13])).
% 1.23/0.52  fof(f13,plain,(
% 1.23/0.52    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.23/0.52  fof(f60,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))) )),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f26,f38])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 1.23/0.52  fof(f165,plain,(
% 1.23/0.52    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.23/0.52    inference(forward_demodulation,[],[f164,f65])).
% 1.23/0.52  fof(f65,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f64,f46])).
% 1.23/0.52  fof(f64,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK0),X0))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f61,f30])).
% 1.23/0.52  fof(f61,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f28,f38])).
% 1.23/0.52  fof(f164,plain,(
% 1.23/0.52    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.23/0.52    inference(trivial_inequality_removal,[],[f163])).
% 1.23/0.52  fof(f163,plain,(
% 1.23/0.52    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.23/0.52    inference(superposition,[],[f35,f122])).
% 1.23/0.52  fof(f122,plain,(
% 1.23/0.52    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f116,f31])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f116,plain,(
% 1.23/0.52    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),sK2)),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f26,f105,f39])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f25])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.23/0.52    inference(flattening,[],[f24])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.23/0.52    inference(nnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.23/0.52    inference(ennf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 1.23/0.52  fof(f105,plain,(
% 1.23/0.52    r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))),k1_relat_1(k7_relat_1(sK0,sK2)))),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f32,f102])).
% 1.23/0.52  fof(f102,plain,(
% 1.23/0.52    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0)) )),
% 1.23/0.52    inference(global_subsumption,[],[f26,f101])).
% 1.23/0.52  fof(f101,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.23/0.52    inference(forward_demodulation,[],[f100,f65])).
% 1.23/0.52  fof(f100,plain,(
% 1.23/0.52    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.23/0.52    inference(forward_demodulation,[],[f98,f66])).
% 1.23/0.52  fof(f98,plain,(
% 1.23/0.52    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.23/0.52    inference(resolution,[],[f97,f36])).
% 1.23/0.52  fof(f97,plain,(
% 1.23/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.23/0.52    inference(global_subsumption,[],[f28,f96])).
% 1.23/0.52  fof(f96,plain,(
% 1.23/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~v1_relat_1(sK1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f95])).
% 1.23/0.52  fof(f95,plain,(
% 1.23/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~v1_relat_1(sK1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.23/0.52    inference(forward_demodulation,[],[f93,f30])).
% 1.23/0.52  fof(f93,plain,(
% 1.23/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~v1_relat_1(sK1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) )),
% 1.23/0.52    inference(resolution,[],[f89,f29])).
% 1.23/0.52  fof(f89,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,X0,X1),X1) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)) )),
% 1.23/0.52    inference(global_subsumption,[],[f26,f87])).
% 1.23/0.52  fof(f87,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(sK0)) )),
% 1.23/0.52    inference(resolution,[],[f34,f27])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.52    inference(rectify,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.52    inference(nnf_transformation,[],[f11])).
% 1.23/0.52  fof(f11,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.52    inference(flattening,[],[f10])).
% 1.23/0.52  fof(f10,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    v1_funct_1(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    v1_relat_1(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    v1_funct_1(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (19619)------------------------------
% 1.23/0.52  % (19619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (19619)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (19619)Memory used [KB]: 10874
% 1.23/0.52  % (19619)Time elapsed: 0.068 s
% 1.23/0.52  % (19619)------------------------------
% 1.23/0.52  % (19619)------------------------------
% 1.23/0.53  % (19604)Success in time 0.168 s
%------------------------------------------------------------------------------
