%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0651+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 388 expanded)
%              Number of leaves         :   10 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (1728 expanded)
%              Number of equality atoms :   63 ( 634 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3850,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3769,f3806,f3843])).

fof(f3843,plain,(
    spl149_2 ),
    inference(avatar_contradiction_clause,[],[f3842])).

fof(f3842,plain,
    ( $false
    | spl149_2 ),
    inference(subsumption_resolution,[],[f3841,f3034])).

fof(f3034,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2030])).

fof(f2030,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1591])).

fof(f1591,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1590])).

fof(f1590,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3841,plain,
    ( ~ r1_tarski(k2_relat_1(sK32),k2_relat_1(sK32))
    | spl149_2 ),
    inference(forward_demodulation,[],[f3840,f3504])).

fof(f3504,plain,(
    k2_relat_1(sK32) = k1_relat_1(k4_relat_1(sK32)) ),
    inference(backward_demodulation,[],[f3494,f3498])).

fof(f3498,plain,(
    k2_funct_1(sK32) = k4_relat_1(sK32) ),
    inference(subsumption_resolution,[],[f3497,f1885])).

fof(f1885,plain,(
    v1_funct_1(sK32) ),
    inference(cnf_transformation,[],[f1532])).

fof(f1532,plain,
    ( ( k1_relat_1(sK32) != k2_relat_1(k5_relat_1(sK32,k2_funct_1(sK32)))
      | k1_relat_1(sK32) != k1_relat_1(k5_relat_1(sK32,k2_funct_1(sK32))) )
    & v2_funct_1(sK32)
    & v1_funct_1(sK32)
    & v1_relat_1(sK32) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32])],[f961,f1531])).

fof(f1531,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK32) != k2_relat_1(k5_relat_1(sK32,k2_funct_1(sK32)))
        | k1_relat_1(sK32) != k1_relat_1(k5_relat_1(sK32,k2_funct_1(sK32))) )
      & v2_funct_1(sK32)
      & v1_funct_1(sK32)
      & v1_relat_1(sK32) ) ),
    introduced(choice_axiom,[])).

fof(f961,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f960])).

fof(f960,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f951])).

fof(f951,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f950])).

fof(f950,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f3497,plain,
    ( k2_funct_1(sK32) = k4_relat_1(sK32)
    | ~ v1_funct_1(sK32) ),
    inference(subsumption_resolution,[],[f3164,f1886])).

fof(f1886,plain,(
    v2_funct_1(sK32) ),
    inference(cnf_transformation,[],[f1532])).

fof(f3164,plain,
    ( k2_funct_1(sK32) = k4_relat_1(sK32)
    | ~ v2_funct_1(sK32)
    | ~ v1_funct_1(sK32) ),
    inference(resolution,[],[f1884,f1938])).

fof(f1938,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1008])).

fof(f1008,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1007])).

fof(f1007,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f894,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1884,plain,(
    v1_relat_1(sK32) ),
    inference(cnf_transformation,[],[f1532])).

fof(f3494,plain,(
    k2_relat_1(sK32) = k1_relat_1(k2_funct_1(sK32)) ),
    inference(subsumption_resolution,[],[f3493,f1885])).

fof(f3493,plain,
    ( k2_relat_1(sK32) = k1_relat_1(k2_funct_1(sK32))
    | ~ v1_funct_1(sK32) ),
    inference(subsumption_resolution,[],[f3162,f1886])).

fof(f3162,plain,
    ( k2_relat_1(sK32) = k1_relat_1(k2_funct_1(sK32))
    | ~ v2_funct_1(sK32)
    | ~ v1_funct_1(sK32) ),
    inference(resolution,[],[f1884,f1936])).

fof(f1936,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1006])).

fof(f1006,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1005])).

fof(f1005,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f947])).

fof(f947,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f3840,plain,
    ( ~ r1_tarski(k2_relat_1(sK32),k1_relat_1(k4_relat_1(sK32)))
    | spl149_2 ),
    inference(subsumption_resolution,[],[f3839,f1884])).

fof(f3839,plain,
    ( ~ r1_tarski(k2_relat_1(sK32),k1_relat_1(k4_relat_1(sK32)))
    | ~ v1_relat_1(sK32)
    | spl149_2 ),
    inference(subsumption_resolution,[],[f3824,f3508])).

fof(f3508,plain,(
    v1_relat_1(k4_relat_1(sK32)) ),
    inference(forward_demodulation,[],[f3507,f3498])).

fof(f3507,plain,(
    v1_relat_1(k2_funct_1(sK32)) ),
    inference(subsumption_resolution,[],[f3165,f1885])).

fof(f3165,plain,
    ( v1_relat_1(k2_funct_1(sK32))
    | ~ v1_funct_1(sK32) ),
    inference(resolution,[],[f1884,f1939])).

fof(f1939,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1010])).

fof(f1010,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1009])).

fof(f1009,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f3824,plain,
    ( ~ r1_tarski(k2_relat_1(sK32),k1_relat_1(k4_relat_1(sK32)))
    | ~ v1_relat_1(k4_relat_1(sK32))
    | ~ v1_relat_1(sK32)
    | spl149_2 ),
    inference(trivial_inequality_removal,[],[f3815])).

fof(f3815,plain,
    ( k1_relat_1(sK32) != k1_relat_1(sK32)
    | ~ r1_tarski(k2_relat_1(sK32),k1_relat_1(k4_relat_1(sK32)))
    | ~ v1_relat_1(k4_relat_1(sK32))
    | ~ v1_relat_1(sK32)
    | spl149_2 ),
    inference(superposition,[],[f3768,f1911])).

fof(f1911,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f993])).

fof(f993,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f992])).

fof(f992,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f845])).

fof(f845,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f3768,plain,
    ( k1_relat_1(sK32) != k1_relat_1(k5_relat_1(sK32,k4_relat_1(sK32)))
    | spl149_2 ),
    inference(avatar_component_clause,[],[f3767])).

fof(f3767,plain,
    ( spl149_2
  <=> k1_relat_1(sK32) = k1_relat_1(k5_relat_1(sK32,k4_relat_1(sK32))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl149_2])])).

fof(f3806,plain,(
    spl149_1 ),
    inference(avatar_contradiction_clause,[],[f3805])).

fof(f3805,plain,
    ( $false
    | spl149_1 ),
    inference(subsumption_resolution,[],[f3804,f3034])).

fof(f3804,plain,
    ( ~ r1_tarski(k2_relat_1(sK32),k2_relat_1(sK32))
    | spl149_1 ),
    inference(forward_demodulation,[],[f3803,f3504])).

fof(f3803,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK32)),k2_relat_1(sK32))
    | spl149_1 ),
    inference(subsumption_resolution,[],[f3802,f3508])).

fof(f3802,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK32)),k2_relat_1(sK32))
    | ~ v1_relat_1(k4_relat_1(sK32))
    | spl149_1 ),
    inference(subsumption_resolution,[],[f3801,f1884])).

fof(f3801,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK32)),k2_relat_1(sK32))
    | ~ v1_relat_1(sK32)
    | ~ v1_relat_1(k4_relat_1(sK32))
    | spl149_1 ),
    inference(subsumption_resolution,[],[f3776,f3505])).

fof(f3505,plain,(
    k1_relat_1(sK32) = k2_relat_1(k4_relat_1(sK32)) ),
    inference(backward_demodulation,[],[f3496,f3498])).

fof(f3496,plain,(
    k1_relat_1(sK32) = k2_relat_1(k2_funct_1(sK32)) ),
    inference(subsumption_resolution,[],[f3495,f1885])).

fof(f3495,plain,
    ( k1_relat_1(sK32) = k2_relat_1(k2_funct_1(sK32))
    | ~ v1_funct_1(sK32) ),
    inference(subsumption_resolution,[],[f3163,f1886])).

fof(f3163,plain,
    ( k1_relat_1(sK32) = k2_relat_1(k2_funct_1(sK32))
    | ~ v2_funct_1(sK32)
    | ~ v1_funct_1(sK32) ),
    inference(resolution,[],[f1884,f1937])).

fof(f1937,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1006])).

fof(f3776,plain,
    ( k1_relat_1(sK32) != k2_relat_1(k4_relat_1(sK32))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK32)),k2_relat_1(sK32))
    | ~ v1_relat_1(sK32)
    | ~ v1_relat_1(k4_relat_1(sK32))
    | spl149_1 ),
    inference(superposition,[],[f3765,f1910])).

fof(f1910,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f991])).

fof(f991,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f990])).

fof(f990,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f846])).

fof(f846,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f3765,plain,
    ( k1_relat_1(sK32) != k2_relat_1(k5_relat_1(sK32,k4_relat_1(sK32)))
    | spl149_1 ),
    inference(avatar_component_clause,[],[f3764])).

fof(f3764,plain,
    ( spl149_1
  <=> k1_relat_1(sK32) = k2_relat_1(k5_relat_1(sK32,k4_relat_1(sK32))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl149_1])])).

fof(f3769,plain,
    ( ~ spl149_1
    | ~ spl149_2 ),
    inference(avatar_split_clause,[],[f3506,f3767,f3764])).

fof(f3506,plain,
    ( k1_relat_1(sK32) != k1_relat_1(k5_relat_1(sK32,k4_relat_1(sK32)))
    | k1_relat_1(sK32) != k2_relat_1(k5_relat_1(sK32,k4_relat_1(sK32))) ),
    inference(forward_demodulation,[],[f3499,f3498])).

fof(f3499,plain,
    ( k1_relat_1(sK32) != k2_relat_1(k5_relat_1(sK32,k4_relat_1(sK32)))
    | k1_relat_1(sK32) != k1_relat_1(k5_relat_1(sK32,k2_funct_1(sK32))) ),
    inference(backward_demodulation,[],[f1887,f3498])).

fof(f1887,plain,
    ( k1_relat_1(sK32) != k2_relat_1(k5_relat_1(sK32,k2_funct_1(sK32)))
    | k1_relat_1(sK32) != k1_relat_1(k5_relat_1(sK32,k2_funct_1(sK32))) ),
    inference(cnf_transformation,[],[f1532])).
%------------------------------------------------------------------------------
