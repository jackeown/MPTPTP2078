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
% DateTime   : Thu Dec  3 13:06:57 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  277 (1666 expanded)
%              Number of leaves         :   36 ( 433 expanded)
%              Depth                    :   31
%              Number of atoms          :  933 (5458 expanded)
%              Number of equality atoms :   88 (1476 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3068,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f207,f269,f367,f376,f430,f578,f592,f1170,f1456,f1465,f1484,f1488,f1689,f2078,f2207,f3041,f3067])).

fof(f3067,plain,
    ( ~ spl6_3
    | ~ spl6_9
    | spl6_12
    | ~ spl6_15
    | ~ spl6_39
    | ~ spl6_46
    | ~ spl6_77 ),
    inference(avatar_contradiction_clause,[],[f3066])).

fof(f3066,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12
    | ~ spl6_15
    | ~ spl6_39
    | ~ spl6_46
    | ~ spl6_77 ),
    inference(subsumption_resolution,[],[f3059,f1763])).

fof(f1763,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f869,f1751])).

fof(f1751,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1750,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1750,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f162,f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f162,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_9
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f869,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f868])).

fof(f868,plain,
    ( spl6_39
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f3059,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12
    | ~ spl6_15
    | ~ spl6_39
    | ~ spl6_46
    | ~ spl6_77 ),
    inference(backward_demodulation,[],[f2764,f2846])).

fof(f2846,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f2844])).

fof(f2844,plain,
    ( spl6_77
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f2764,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12
    | ~ spl6_15
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f2746,f2230])).

fof(f2230,plain,
    ( k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f1761,f2214])).

fof(f2214,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f2213,f92])).

fof(f2213,plain,
    ( sK0 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f1169,f120])).

fof(f1169,plain,
    ( sK0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1167,plain,
    ( spl6_46
  <=> sK0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f1761,plain,
    ( k1_xboole_0 = sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f1760,f92])).

fof(f1760,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f1759,f120])).

fof(f1759,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f268,f1751])).

fof(f268,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,sK2))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_15
  <=> k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f2746,plain,
    ( r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f2712,f2263])).

fof(f2263,plain,
    ( k1_xboole_0 != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f2012,f2214])).

fof(f2012,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12 ),
    inference(forward_demodulation,[],[f2011,f120])).

fof(f2011,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,sK1,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | spl6_12 ),
    inference(forward_demodulation,[],[f191,f1751])).

fof(f191,plain,
    ( k1_xboole_0 != k5_partfun1(sK0,sK1,sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_12
  <=> k1_xboole_0 = k5_partfun1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2712,plain,
    ( k1_xboole_0 = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(resolution,[],[f2564,f2257])).

fof(f2257,plain,
    ( ! [X12] :
        ( ~ r2_hidden(X12,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
        | r2_hidden(X12,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f1974,f2214])).

fof(f1974,plain,
    ( ! [X12] :
        ( ~ r2_hidden(X12,k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))
        | r2_hidden(X12,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1973,f120])).

fof(f1973,plain,
    ( ! [X12] :
        ( ~ r2_hidden(X12,k5_partfun1(sK0,sK1,k1_xboole_0))
        | r2_hidden(X12,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1972,f1751])).

fof(f1972,plain,
    ( ! [X12] :
        ( r2_hidden(X12,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X12,k5_partfun1(sK0,sK1,sK2)) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f1971,f92])).

fof(f1971,plain,
    ( ! [X12] :
        ( r2_hidden(X12,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | ~ r2_hidden(X12,k5_partfun1(sK0,sK1,sK2)) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f235,f120])).

fof(f235,plain,(
    ! [X12] :
      ( r2_hidden(X12,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X12,k5_partfun1(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f227,f60])).

fof(f60,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f227,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k5_partfun1(sK0,sK1,sK2))
      | r2_hidden(X12,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f107,plain,(
    ! [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(f97,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f57,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2564,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2543,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2543,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | k1_xboole_0 = X2 )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2444,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2444,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f1792,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1792,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(sK5(X3,k1_xboole_0),X3) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f1791,f1751])).

fof(f1791,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(sK5(X3,sK2),X3) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f1790,f1763])).

fof(f1790,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,X3)
        | r2_hidden(sK5(X3,sK2),X3) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f1789,f92])).

fof(f1789,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_zfmisc_1(sK0,k1_xboole_0))
        | ~ r2_hidden(X2,X3)
        | r2_hidden(sK5(X3,sK2),X3) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f1424,f120])).

fof(f1424,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k2_zfmisc_1(sK0,sK1))
      | r2_hidden(sK5(X3,sK2),X3) ) ),
    inference(resolution,[],[f214,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f214,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,sK2)
      | ~ r2_hidden(X3,X2)
      | r2_hidden(X3,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f152,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f152,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f102,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f102,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3041,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_15
    | ~ spl6_39
    | ~ spl6_46
    | spl6_77 ),
    inference(avatar_contradiction_clause,[],[f3040])).

fof(f3040,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_15
    | ~ spl6_39
    | ~ spl6_46
    | spl6_77 ),
    inference(subsumption_resolution,[],[f3036,f2234])).

fof(f2234,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f1818,f2214])).

fof(f1818,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f1817,f1761])).

fof(f1817,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),sK0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1816,f1751])).

fof(f1816,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2)),sK0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f1395,f120])).

fof(f1395,plain,(
    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1) ),
    inference(resolution,[],[f1241,f106])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_2(X1,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f96,f56])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_2(X1,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f57,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1241,plain,(
    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f242,f63])).

fof(f242,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f144,f62])).

fof(f144,plain,(
    r2_hidden(sK5(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f58,f75])).

fof(f58,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f3036,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_46
    | spl6_77 ),
    inference(resolution,[],[f3019,f3005])).

fof(f3005,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f3001,f2269])).

fof(f2269,plain,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f2047,f2214])).

fof(f2047,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f2046,f1751])).

fof(f2046,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f58,f120])).

fof(f3001,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(superposition,[],[f76,f2568])).

fof(f2568,plain,
    ( k1_xboole_0 = sK5(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_46 ),
    inference(resolution,[],[f2543,f2248])).

fof(f2248,plain,
    ( v1_xboole_0(sK5(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_46 ),
    inference(backward_demodulation,[],[f1908,f2214])).

fof(f1908,plain,
    ( v1_xboole_0(sK5(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1907,f1751])).

fof(f1907,plain,
    ( v1_xboole_0(sK5(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1306,f120])).

fof(f1306,plain,
    ( v1_xboole_0(sK5(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl6_5 ),
    inference(resolution,[],[f594,f144])).

fof(f594,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,k5_partfun1(sK0,sK1,sK2))
        | v1_xboole_0(X8) )
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f224,f129])).

fof(f129,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f224,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k5_partfun1(sK0,sK1,sK2))
      | v1_xboole_0(X8)
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3019,plain,
    ( ! [X18] :
        ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X18) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(subsumption_resolution,[],[f3018,f2051])).

fof(f2051,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f56,f1751])).

fof(f3018,plain,
    ( ! [X18] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X18)
        | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(forward_demodulation,[],[f3017,f2473])).

fof(f2473,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2460,f64])).

fof(f2460,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f2458,f1763])).

fof(f2458,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))
        | r2_hidden(X1,k1_xboole_0) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2454,f74])).

fof(f2454,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2449,f77])).

fof(f2449,plain,
    ( m1_subset_1(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f2447,f60])).

fof(f2447,plain,
    ( m1_subset_1(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2442,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2442,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f1792,f2024])).

fof(f2024,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f2023,f1751])).

fof(f2023,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f2022,f92])).

fof(f2022,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f141,f120])).

fof(f141,plain,(
    r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f103,f60])).

fof(f103,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f57,f65])).

fof(f3017,plain,
    ( ! [X18] :
        ( ~ v1_funct_1(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X18)
        | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(forward_demodulation,[],[f2979,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2979,plain,
    ( ! [X18] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X18)
        | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(forward_demodulation,[],[f2978,f2473])).

fof(f2978,plain,
    ( ! [X18] :
        ( ~ v1_funct_2(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_xboole_0,X18)
        | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(forward_demodulation,[],[f2977,f93])).

fof(f2977,plain,
    ( ! [X18] :
        ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(forward_demodulation,[],[f2976,f2473])).

fof(f2976,plain,
    ( ! [X18] :
        ( r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(forward_demodulation,[],[f2975,f93])).

fof(f2975,plain,
    ( ! [X18] :
        ( r2_hidden(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39
    | spl6_77 ),
    inference(subsumption_resolution,[],[f2974,f2845])).

fof(f2845,plain,
    ( k1_xboole_0 != k1_zfmisc_1(k1_xboole_0)
    | spl6_77 ),
    inference(avatar_component_clause,[],[f2844])).

fof(f2974,plain,
    ( ! [X18] :
        ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
        | r2_hidden(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f2969,f93])).

fof(f2969,plain,
    ( ! [X18] :
        ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))
        | r2_hidden(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_funct_2(k1_xboole_0,X18))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0)) )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2959,f94])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f2959,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(duplicate_literal_removal,[],[f2952])).

fof(f2952,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2542,f2543])).

fof(f2542,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | m1_subset_1(sK5(X1,k1_xboole_0),X1)
        | k1_xboole_0 = X1 )
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_39 ),
    inference(resolution,[],[f2444,f66])).

fof(f2207,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f2206])).

fof(f2206,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | spl6_43 ),
    inference(subsumption_resolution,[],[f2205,f126])).

fof(f126,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2205,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_3
    | spl6_43 ),
    inference(resolution,[],[f2170,f62])).

fof(f2170,plain,
    ( r2_hidden(sK5(sK0,k1_xboole_0),sK0)
    | ~ spl6_3
    | spl6_43 ),
    inference(resolution,[],[f2075,f75])).

fof(f2075,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl6_3
    | spl6_43 ),
    inference(forward_demodulation,[],[f2074,f92])).

fof(f2074,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_3
    | spl6_43 ),
    inference(forward_demodulation,[],[f1150,f120])).

fof(f1150,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK0,sK1))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1149,plain,
    ( spl6_43
  <=> r1_tarski(sK0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f2078,plain,
    ( ~ spl6_3
    | ~ spl6_9
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f2077])).

fof(f2077,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_9
    | spl6_40 ),
    inference(subsumption_resolution,[],[f901,f1751])).

fof(f901,plain,
    ( k1_xboole_0 != sK2
    | spl6_40 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl6_40
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f1689,plain,
    ( ~ spl6_9
    | ~ spl6_39
    | ~ spl6_40
    | spl6_45 ),
    inference(avatar_contradiction_clause,[],[f1688])).

fof(f1688,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_39
    | ~ spl6_40
    | spl6_45 ),
    inference(subsumption_resolution,[],[f1629,f1600])).

fof(f1600,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f869,f902])).

fof(f902,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f900])).

fof(f1629,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_9
    | ~ spl6_40
    | spl6_45 ),
    inference(backward_demodulation,[],[f1190,f1618])).

fof(f1618,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_9
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f162,f902])).

fof(f1190,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),k2_zfmisc_1(sK0,sK1))
    | spl6_45 ),
    inference(resolution,[],[f1165,f75])).

fof(f1165,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK0)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1163,plain,
    ( spl6_45
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f1488,plain,
    ( spl6_3
    | spl6_20 ),
    inference(avatar_split_clause,[],[f1487,f300,f118])).

fof(f300,plain,
    ( spl6_20
  <=> ! [X6] :
        ( ~ r2_hidden(X6,k5_partfun1(sK0,sK1,sK2))
        | r2_hidden(X6,k1_funct_2(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1487,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k5_partfun1(sK0,sK1,sK2))
      | k1_xboole_0 = sK1
      | r2_hidden(X6,k1_funct_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1486,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f95,f56])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_1(X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f57,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1486,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k5_partfun1(sK0,sK1,sK2))
      | k1_xboole_0 = sK1
      | r2_hidden(X6,k1_funct_2(sK0,sK1))
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f1262,f106])).

fof(f1262,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k5_partfun1(sK0,sK1,sK2))
      | k1_xboole_0 = sK1
      | r2_hidden(X6,k1_funct_2(sK0,sK1))
      | ~ v1_funct_2(X6,sK0,sK1)
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f107,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1484,plain,
    ( ~ spl6_10
    | spl6_39 ),
    inference(avatar_split_clause,[],[f1483,f868,f180])).

fof(f180,plain,
    ( spl6_10
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1483,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f1303])).

fof(f1303,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f153,f62])).

fof(f153,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f102,f74])).

fof(f1465,plain,
    ( ~ spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f892,f160,f156])).

fof(f156,plain,
    ( spl6_8
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f892,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f102,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1456,plain,(
    ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f1455])).

fof(f1455,plain,
    ( $false
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f1452,f58])).

fof(f1452,plain,
    ( r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    | ~ spl6_20 ),
    inference(resolution,[],[f1327,f76])).

fof(f1327,plain,
    ( r2_hidden(sK5(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl6_20 ),
    inference(resolution,[],[f301,f144])).

fof(f301,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k5_partfun1(sK0,sK1,sK2))
        | r2_hidden(X6,k1_funct_2(sK0,sK1)) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f300])).

fof(f1170,plain,
    ( ~ spl6_45
    | spl6_46
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f1161,f1149,f1167,f1163])).

fof(f1161,plain,
    ( sK0 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK0)
    | ~ spl6_43 ),
    inference(resolution,[],[f1151,f73])).

fof(f1151,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f592,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f242,f134])).

fof(f134,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_6
  <=> v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f578,plain,
    ( ~ spl6_3
    | ~ spl6_9
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_9
    | spl6_14 ),
    inference(subsumption_resolution,[],[f576,f492])).

fof(f492,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f437,f442])).

fof(f442,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f441,f92])).

fof(f441,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f162,f120])).

fof(f437,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f436,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f436,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f435,f92])).

fof(f435,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f217,f120])).

fof(f217,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f153,f62])).

fof(f576,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))),k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_9
    | spl6_14 ),
    inference(resolution,[],[f485,f75])).

fof(f485,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_9
    | spl6_14 ),
    inference(backward_demodulation,[],[f407,f442])).

fof(f407,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k5_partfun1(sK0,k1_xboole_0,sK2)))
    | ~ spl6_3
    | spl6_14 ),
    inference(forward_demodulation,[],[f352,f92])).

fof(f352,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3(k5_partfun1(sK0,k1_xboole_0,sK2)))
    | ~ spl6_3
    | spl6_14 ),
    inference(backward_demodulation,[],[f264,f120])).

fof(f264,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k5_partfun1(sK0,sK1,sK2)))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_14
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f430,plain,
    ( ~ spl6_3
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl6_3
    | spl6_8 ),
    inference(subsumption_resolution,[],[f428,f59])).

fof(f428,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_3
    | spl6_8 ),
    inference(forward_demodulation,[],[f427,f92])).

fof(f427,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_3
    | spl6_8 ),
    inference(forward_demodulation,[],[f256,f120])).

fof(f256,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_8 ),
    inference(resolution,[],[f174,f62])).

fof(f174,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1))
    | spl6_8 ),
    inference(resolution,[],[f158,f75])).

fof(f158,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f376,plain,
    ( ~ spl6_3
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl6_3
    | spl6_10 ),
    inference(subsumption_resolution,[],[f374,f59])).

fof(f374,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_3
    | spl6_10 ),
    inference(forward_demodulation,[],[f324,f92])).

fof(f324,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_3
    | spl6_10 ),
    inference(backward_demodulation,[],[f182,f120])).

fof(f182,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f367,plain,
    ( ~ spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl6_3
    | spl6_5 ),
    inference(subsumption_resolution,[],[f312,f59])).

fof(f312,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_3
    | spl6_5 ),
    inference(backward_demodulation,[],[f130,f120])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f269,plain,
    ( ~ spl6_14
    | spl6_15
    | spl6_6 ),
    inference(avatar_split_clause,[],[f260,f132,f266,f262])).

fof(f260,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k5_partfun1(sK0,sK1,sK2)))
    | spl6_6 ),
    inference(resolution,[],[f251,f73])).

fof(f251,plain,
    ( r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK1))
    | spl6_6 ),
    inference(resolution,[],[f226,f173])).

fof(f173,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2))
    | spl6_6 ),
    inference(resolution,[],[f133,f63])).

fof(f133,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f226,plain,(
    ! [X11] :
      ( ~ r2_hidden(X11,k5_partfun1(sK0,sK1,sK2))
      | r1_tarski(X11,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f107,f77])).

fof(f207,plain,
    ( spl6_6
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f202,f59])).

fof(f202,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_6
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f133,f192])).

fof(f192,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f135,plain,
    ( spl6_4
    | ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f122,f132,f128,f124])).

fof(f122,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f56])).

fof(f99,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f57,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (16780)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (16781)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (16797)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (16795)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (16787)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (16772)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (16786)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16773)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (16779)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (16799)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (16791)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (16777)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (16774)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (16776)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (16775)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (16788)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (16783)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (16793)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (16789)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (16798)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (16794)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (16790)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (16792)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (16785)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (16782)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (16778)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.55  % (16784)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.55  % (16800)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (16796)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % (16801)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.61/0.62  % (16780)Refutation found. Thanks to Tanya!
% 1.61/0.62  % SZS status Theorem for theBenchmark
% 1.61/0.62  % SZS output start Proof for theBenchmark
% 1.61/0.62  fof(f3068,plain,(
% 1.61/0.62    $false),
% 1.61/0.62    inference(avatar_sat_refutation,[],[f135,f207,f269,f367,f376,f430,f578,f592,f1170,f1456,f1465,f1484,f1488,f1689,f2078,f2207,f3041,f3067])).
% 1.61/0.62  fof(f3067,plain,(
% 1.61/0.62    ~spl6_3 | ~spl6_9 | spl6_12 | ~spl6_15 | ~spl6_39 | ~spl6_46 | ~spl6_77),
% 1.61/0.62    inference(avatar_contradiction_clause,[],[f3066])).
% 1.61/0.62  fof(f3066,plain,(
% 1.61/0.62    $false | (~spl6_3 | ~spl6_9 | spl6_12 | ~spl6_15 | ~spl6_39 | ~spl6_46 | ~spl6_77)),
% 1.61/0.62    inference(subsumption_resolution,[],[f3059,f1763])).
% 1.61/0.62  fof(f1763,plain,(
% 1.61/0.62    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 1.61/0.62    inference(forward_demodulation,[],[f869,f1751])).
% 1.61/0.62  fof(f1751,plain,(
% 1.61/0.62    k1_xboole_0 = sK2 | (~spl6_3 | ~spl6_9)),
% 1.61/0.62    inference(forward_demodulation,[],[f1750,f92])).
% 1.61/0.62  fof(f92,plain,(
% 1.61/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.61/0.62    inference(equality_resolution,[],[f81])).
% 1.61/0.62  fof(f81,plain,(
% 1.61/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.61/0.62    inference(cnf_transformation,[],[f55])).
% 1.61/0.62  fof(f55,plain,(
% 1.61/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.61/0.62    inference(flattening,[],[f54])).
% 1.61/0.62  fof(f54,plain,(
% 1.61/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.61/0.62    inference(nnf_transformation,[],[f7])).
% 1.61/0.62  fof(f7,axiom,(
% 1.61/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.61/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.61/0.62  fof(f1750,plain,(
% 1.61/0.62    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl6_3 | ~spl6_9)),
% 1.61/0.62    inference(forward_demodulation,[],[f162,f120])).
% 1.61/0.62  fof(f120,plain,(
% 1.61/0.62    k1_xboole_0 = sK1 | ~spl6_3),
% 1.61/0.62    inference(avatar_component_clause,[],[f118])).
% 1.61/0.62  fof(f118,plain,(
% 1.61/0.62    spl6_3 <=> k1_xboole_0 = sK1),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.61/0.62  fof(f162,plain,(
% 1.61/0.62    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl6_9),
% 1.61/0.62    inference(avatar_component_clause,[],[f160])).
% 1.61/0.62  fof(f160,plain,(
% 1.61/0.62    spl6_9 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.61/0.62  fof(f869,plain,(
% 1.61/0.62    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl6_39),
% 1.61/0.62    inference(avatar_component_clause,[],[f868])).
% 1.61/0.62  fof(f868,plain,(
% 1.61/0.62    spl6_39 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.61/0.62  fof(f3059,plain,(
% 1.61/0.62    r2_hidden(k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_9 | spl6_12 | ~spl6_15 | ~spl6_39 | ~spl6_46 | ~spl6_77)),
% 1.61/0.62    inference(backward_demodulation,[],[f2764,f2846])).
% 1.61/0.62  fof(f2846,plain,(
% 1.61/0.62    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | ~spl6_77),
% 1.61/0.62    inference(avatar_component_clause,[],[f2844])).
% 1.61/0.62  fof(f2844,plain,(
% 1.61/0.62    spl6_77 <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 1.61/0.62  fof(f2764,plain,(
% 1.61/0.62    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9 | spl6_12 | ~spl6_15 | ~spl6_39 | ~spl6_46)),
% 1.61/0.62    inference(forward_demodulation,[],[f2746,f2230])).
% 1.61/0.62  fof(f2230,plain,(
% 1.61/0.62    k1_xboole_0 = sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_15 | ~spl6_46)),
% 1.61/0.62    inference(backward_demodulation,[],[f1761,f2214])).
% 1.61/0.62  fof(f2214,plain,(
% 1.61/0.62    k1_xboole_0 = sK0 | (~spl6_3 | ~spl6_46)),
% 1.61/0.62    inference(forward_demodulation,[],[f2213,f92])).
% 1.61/0.62  fof(f2213,plain,(
% 1.61/0.62    sK0 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl6_3 | ~spl6_46)),
% 1.61/0.62    inference(forward_demodulation,[],[f1169,f120])).
% 1.61/0.62  fof(f1169,plain,(
% 1.61/0.62    sK0 = k2_zfmisc_1(sK0,sK1) | ~spl6_46),
% 1.61/0.62    inference(avatar_component_clause,[],[f1167])).
% 1.61/0.62  fof(f1167,plain,(
% 1.61/0.62    spl6_46 <=> sK0 = k2_zfmisc_1(sK0,sK1)),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.61/0.62  fof(f1761,plain,(
% 1.61/0.62    k1_xboole_0 = sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_15)),
% 1.61/0.62    inference(forward_demodulation,[],[f1760,f92])).
% 1.61/0.62  fof(f1760,plain,(
% 1.61/0.62    k2_zfmisc_1(sK0,k1_xboole_0) = sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_15)),
% 1.61/0.62    inference(forward_demodulation,[],[f1759,f120])).
% 1.61/0.62  fof(f1759,plain,(
% 1.61/0.62    k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_15)),
% 1.61/0.62    inference(forward_demodulation,[],[f268,f1751])).
% 1.61/0.62  fof(f268,plain,(
% 1.61/0.62    k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,sK2)) | ~spl6_15),
% 1.61/0.62    inference(avatar_component_clause,[],[f266])).
% 1.61/0.62  fof(f266,plain,(
% 1.61/0.62    spl6_15 <=> k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,sK2))),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.61/0.62  fof(f2746,plain,(
% 1.61/0.62    r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9 | spl6_12 | ~spl6_39 | ~spl6_46)),
% 1.61/0.62    inference(subsumption_resolution,[],[f2712,f2263])).
% 1.61/0.62  fof(f2263,plain,(
% 1.61/0.62    k1_xboole_0 != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_9 | spl6_12 | ~spl6_46)),
% 1.61/0.62    inference(backward_demodulation,[],[f2012,f2214])).
% 1.61/0.62  fof(f2012,plain,(
% 1.61/0.62    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_9 | spl6_12)),
% 1.61/0.62    inference(forward_demodulation,[],[f2011,f120])).
% 1.61/0.62  fof(f2011,plain,(
% 1.61/0.62    k1_xboole_0 != k5_partfun1(sK0,sK1,k1_xboole_0) | (~spl6_3 | ~spl6_9 | spl6_12)),
% 1.61/0.62    inference(forward_demodulation,[],[f191,f1751])).
% 1.61/0.62  fof(f191,plain,(
% 1.61/0.62    k1_xboole_0 != k5_partfun1(sK0,sK1,sK2) | spl6_12),
% 1.61/0.62    inference(avatar_component_clause,[],[f190])).
% 1.61/0.62  fof(f190,plain,(
% 1.61/0.62    spl6_12 <=> k1_xboole_0 = k5_partfun1(sK0,sK1,sK2)),
% 1.61/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.61/0.62  fof(f2712,plain,(
% 1.61/0.62    k1_xboole_0 = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_39 | ~spl6_46)),
% 1.61/0.62    inference(resolution,[],[f2564,f2257])).
% 1.61/0.62  fof(f2257,plain,(
% 1.61/0.62    ( ! [X12] : (~r2_hidden(X12,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | r2_hidden(X12,k1_zfmisc_1(k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_46)),
% 1.61/0.62    inference(backward_demodulation,[],[f1974,f2214])).
% 1.61/0.62  fof(f1974,plain,(
% 1.61/0.62    ( ! [X12] : (~r2_hidden(X12,k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)) | r2_hidden(X12,k1_zfmisc_1(k1_xboole_0))) ) | (~spl6_3 | ~spl6_9)),
% 1.61/0.62    inference(forward_demodulation,[],[f1973,f120])).
% 1.61/0.62  fof(f1973,plain,(
% 1.61/0.62    ( ! [X12] : (~r2_hidden(X12,k5_partfun1(sK0,sK1,k1_xboole_0)) | r2_hidden(X12,k1_zfmisc_1(k1_xboole_0))) ) | (~spl6_3 | ~spl6_9)),
% 1.61/0.62    inference(forward_demodulation,[],[f1972,f1751])).
% 1.61/0.62  fof(f1972,plain,(
% 1.61/0.62    ( ! [X12] : (r2_hidden(X12,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X12,k5_partfun1(sK0,sK1,sK2))) ) | ~spl6_3),
% 1.61/0.62    inference(forward_demodulation,[],[f1971,f92])).
% 1.61/0.62  fof(f1971,plain,(
% 1.61/0.62    ( ! [X12] : (r2_hidden(X12,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~r2_hidden(X12,k5_partfun1(sK0,sK1,sK2))) ) | ~spl6_3),
% 1.61/0.62    inference(forward_demodulation,[],[f235,f120])).
% 1.61/0.62  fof(f235,plain,(
% 1.61/0.62    ( ! [X12] : (r2_hidden(X12,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X12,k5_partfun1(sK0,sK1,sK2))) )),
% 1.61/0.62    inference(subsumption_resolution,[],[f227,f60])).
% 1.61/0.62  fof(f60,plain,(
% 1.61/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.61/0.62    inference(cnf_transformation,[],[f9])).
% 1.61/0.62  fof(f9,axiom,(
% 1.61/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.61/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.61/0.62  fof(f227,plain,(
% 1.61/0.62    ( ! [X12] : (~r2_hidden(X12,k5_partfun1(sK0,sK1,sK2)) | r2_hidden(X12,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.61/0.62    inference(resolution,[],[f107,f65])).
% 1.61/0.63  fof(f65,plain,(
% 1.61/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.61/0.63    inference(cnf_transformation,[],[f46])).
% 1.61/0.63  fof(f46,plain,(
% 1.61/0.63    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.61/0.63    inference(nnf_transformation,[],[f23])).
% 1.61/0.63  fof(f23,plain,(
% 1.61/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.61/0.63    inference(ennf_transformation,[],[f8])).
% 1.61/0.63  fof(f8,axiom,(
% 1.61/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.61/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.61/0.63  fof(f107,plain,(
% 1.61/0.63    ( ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X2,k5_partfun1(sK0,sK1,sK2))) )),
% 1.61/0.63    inference(subsumption_resolution,[],[f97,f56])).
% 1.61/0.63  fof(f56,plain,(
% 1.61/0.63    v1_funct_1(sK2)),
% 1.61/0.63    inference(cnf_transformation,[],[f39])).
% 1.61/0.63  fof(f39,plain,(
% 1.61/0.63    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 1.61/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f38])).
% 1.61/0.63  fof(f38,plain,(
% 1.61/0.63    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 1.61/0.63    introduced(choice_axiom,[])).
% 1.61/0.63  fof(f21,plain,(
% 1.61/0.63    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.61/0.63    inference(flattening,[],[f20])).
% 1.61/0.63  fof(f20,plain,(
% 1.61/0.63    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.61/0.63    inference(ennf_transformation,[],[f19])).
% 1.61/0.63  fof(f19,negated_conjecture,(
% 1.61/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.61/0.63    inference(negated_conjecture,[],[f18])).
% 1.61/0.63  fof(f18,conjecture,(
% 1.61/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.61/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).
% 1.61/0.63  fof(f97,plain,(
% 1.61/0.63    ( ! [X2] : (~r2_hidden(X2,k5_partfun1(sK0,sK1,sK2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)) )),
% 1.61/0.63    inference(resolution,[],[f57,f87])).
% 1.61/0.63  fof(f87,plain,(
% 1.61/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.61/0.63    inference(cnf_transformation,[],[f33])).
% 1.61/0.63  fof(f33,plain,(
% 1.61/0.63    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.61/0.63    inference(flattening,[],[f32])).
% 1.61/0.63  fof(f32,plain,(
% 1.61/0.63    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.61/0.63    inference(ennf_transformation,[],[f17])).
% 1.61/0.63  fof(f17,axiom,(
% 1.61/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.61/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 1.61/0.63  fof(f57,plain,(
% 1.61/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.61/0.63    inference(cnf_transformation,[],[f39])).
% 1.61/0.63  fof(f2564,plain,(
% 1.61/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 1.61/0.63    inference(resolution,[],[f2543,f63])).
% 1.61/0.63  fof(f63,plain,(
% 1.61/0.63    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.61/0.63    inference(cnf_transformation,[],[f43])).
% 1.61/0.63  fof(f43,plain,(
% 1.61/0.63    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 1.61/0.63  fof(f42,plain,(
% 1.61/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.61/0.63    introduced(choice_axiom,[])).
% 1.61/0.63  fof(f41,plain,(
% 1.61/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.63    inference(rectify,[],[f40])).
% 1.61/0.63  fof(f40,plain,(
% 1.61/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.61/0.63    inference(nnf_transformation,[],[f1])).
% 1.61/0.63  fof(f1,axiom,(
% 1.61/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.61/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.61/0.63  fof(f2543,plain,(
% 1.61/0.63    ( ! [X2] : (~v1_xboole_0(X2) | k1_xboole_0 = X2) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 1.61/0.63    inference(resolution,[],[f2444,f62])).
% 1.61/0.63  fof(f62,plain,(
% 1.61/0.63    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.61/0.63    inference(cnf_transformation,[],[f43])).
% 1.61/0.63  fof(f2444,plain,(
% 1.61/0.63    ( ! [X0] : (r2_hidden(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 1.61/0.63    inference(resolution,[],[f1792,f64])).
% 1.61/0.63  fof(f64,plain,(
% 1.61/0.63    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.61/0.63    inference(cnf_transformation,[],[f45])).
% 1.61/0.63  fof(f45,plain,(
% 1.61/0.63    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.61/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f44])).
% 1.61/0.63  fof(f44,plain,(
% 1.61/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.61/0.63    introduced(choice_axiom,[])).
% 1.61/0.63  fof(f22,plain,(
% 1.61/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.61/0.63    inference(ennf_transformation,[],[f4])).
% 1.61/0.63  fof(f4,axiom,(
% 1.61/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.61/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.61/0.63  fof(f1792,plain,(
% 1.61/0.63    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(sK5(X3,k1_xboole_0),X3)) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 1.61/0.63    inference(forward_demodulation,[],[f1791,f1751])).
% 1.61/0.63  fof(f1791,plain,(
% 1.61/0.63    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(sK5(X3,sK2),X3)) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 1.61/0.63    inference(subsumption_resolution,[],[f1790,f1763])).
% 1.61/0.63  fof(f1790,plain,(
% 1.61/0.63    ( ! [X2,X3] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,X3) | r2_hidden(sK5(X3,sK2),X3)) ) | ~spl6_3),
% 1.61/0.63    inference(forward_demodulation,[],[f1789,f92])).
% 1.61/0.63  fof(f1789,plain,(
% 1.61/0.63    ( ! [X2,X3] : (r2_hidden(X2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(X2,X3) | r2_hidden(sK5(X3,sK2),X3)) ) | ~spl6_3),
% 1.61/0.63    inference(forward_demodulation,[],[f1424,f120])).
% 1.61/0.63  fof(f1424,plain,(
% 1.61/0.63    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(X2,k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK5(X3,sK2),X3)) )),
% 1.61/0.63    inference(resolution,[],[f214,f75])).
% 1.61/0.63  fof(f75,plain,(
% 1.61/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.61/0.63    inference(cnf_transformation,[],[f52])).
% 1.61/0.63  fof(f52,plain,(
% 1.61/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.61/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 1.61/0.63  fof(f51,plain,(
% 1.61/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.61/0.63    introduced(choice_axiom,[])).
% 1.61/0.63  fof(f50,plain,(
% 1.61/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.61/0.63    inference(rectify,[],[f49])).
% 2.08/0.63  fof(f49,plain,(
% 2.08/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.63    inference(nnf_transformation,[],[f27])).
% 2.08/0.63  fof(f27,plain,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f2])).
% 2.08/0.63  fof(f2,axiom,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.08/0.63  fof(f214,plain,(
% 2.08/0.63    ( ! [X2,X3] : (~r1_tarski(X2,sK2) | ~r2_hidden(X3,X2) | r2_hidden(X3,k2_zfmisc_1(sK0,sK1))) )),
% 2.08/0.63    inference(resolution,[],[f152,f74])).
% 2.08/0.63  fof(f74,plain,(
% 2.08/0.63    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f52])).
% 2.08/0.63  fof(f152,plain,(
% 2.08/0.63    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X0,sK2)) )),
% 2.08/0.63    inference(resolution,[],[f102,f88])).
% 2.08/0.63  fof(f88,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f35])).
% 2.08/0.63  fof(f35,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.63    inference(flattening,[],[f34])).
% 2.08/0.63  fof(f34,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.63    inference(ennf_transformation,[],[f6])).
% 2.08/0.63  fof(f6,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.08/0.63  fof(f102,plain,(
% 2.08/0.63    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 2.08/0.63    inference(resolution,[],[f57,f77])).
% 2.08/0.63  fof(f77,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f53])).
% 2.08/0.63  fof(f53,plain,(
% 2.08/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.08/0.63    inference(nnf_transformation,[],[f11])).
% 2.08/0.63  fof(f11,axiom,(
% 2.08/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.08/0.63  fof(f3041,plain,(
% 2.08/0.63    ~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_15 | ~spl6_39 | ~spl6_46 | spl6_77),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f3040])).
% 2.08/0.63  fof(f3040,plain,(
% 2.08/0.63    $false | (~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_15 | ~spl6_39 | ~spl6_46 | spl6_77)),
% 2.08/0.63    inference(subsumption_resolution,[],[f3036,f2234])).
% 2.08/0.63  fof(f2234,plain,(
% 2.08/0.63    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_9 | ~spl6_15 | ~spl6_46)),
% 2.08/0.63    inference(backward_demodulation,[],[f1818,f2214])).
% 2.08/0.63  fof(f1818,plain,(
% 2.08/0.63    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl6_3 | ~spl6_9 | ~spl6_15)),
% 2.08/0.63    inference(forward_demodulation,[],[f1817,f1761])).
% 2.08/0.63  fof(f1817,plain,(
% 2.08/0.63    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),sK0,k1_xboole_0) | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f1816,f1751])).
% 2.08/0.63  fof(f1816,plain,(
% 2.08/0.63    v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2)),sK0,k1_xboole_0) | ~spl6_3),
% 2.08/0.63    inference(forward_demodulation,[],[f1395,f120])).
% 2.08/0.63  fof(f1395,plain,(
% 2.08/0.63    v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1)),
% 2.08/0.63    inference(resolution,[],[f1241,f106])).
% 2.08/0.63  fof(f106,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,sK1,sK2)) | v1_funct_2(X1,sK0,sK1)) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f96,f56])).
% 2.08/0.63  fof(f96,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,sK1,sK2)) | v1_funct_2(X1,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 2.08/0.63    inference(resolution,[],[f57,f86])).
% 2.08/0.63  fof(f86,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f33])).
% 2.08/0.63  fof(f1241,plain,(
% 2.08/0.63    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2))),
% 2.08/0.63    inference(resolution,[],[f242,f63])).
% 2.08/0.63  fof(f242,plain,(
% 2.08/0.63    ~v1_xboole_0(k5_partfun1(sK0,sK1,sK2))),
% 2.08/0.63    inference(resolution,[],[f144,f62])).
% 2.08/0.63  fof(f144,plain,(
% 2.08/0.63    r2_hidden(sK5(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))),
% 2.08/0.63    inference(resolution,[],[f58,f75])).
% 2.08/0.63  fof(f58,plain,(
% 2.08/0.63    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 2.08/0.63    inference(cnf_transformation,[],[f39])).
% 2.08/0.63  fof(f3036,plain,(
% 2.08/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_39 | ~spl6_46 | spl6_77)),
% 2.08/0.63    inference(resolution,[],[f3019,f3005])).
% 2.08/0.63  fof(f3005,plain,(
% 2.08/0.63    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_39 | ~spl6_46)),
% 2.08/0.63    inference(subsumption_resolution,[],[f3001,f2269])).
% 2.08/0.63  fof(f2269,plain,(
% 2.08/0.63    ~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_46)),
% 2.08/0.63    inference(backward_demodulation,[],[f2047,f2214])).
% 2.08/0.63  fof(f2047,plain,(
% 2.08/0.63    ~r1_tarski(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0)) | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f2046,f1751])).
% 2.08/0.63  fof(f2046,plain,(
% 2.08/0.63    ~r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)) | ~spl6_3),
% 2.08/0.63    inference(forward_demodulation,[],[f58,f120])).
% 2.08/0.63  fof(f3001,plain,(
% 2.08/0.63    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_39 | ~spl6_46)),
% 2.08/0.63    inference(superposition,[],[f76,f2568])).
% 2.08/0.63  fof(f2568,plain,(
% 2.08/0.63    k1_xboole_0 = sK5(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | (~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_39 | ~spl6_46)),
% 2.08/0.63    inference(resolution,[],[f2543,f2248])).
% 2.08/0.63  fof(f2248,plain,(
% 2.08/0.63    v1_xboole_0(sK5(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))) | (~spl6_3 | ~spl6_5 | ~spl6_9 | ~spl6_46)),
% 2.08/0.63    inference(backward_demodulation,[],[f1908,f2214])).
% 2.08/0.63  fof(f1908,plain,(
% 2.08/0.63    v1_xboole_0(sK5(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0),k1_funct_2(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_5 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f1907,f1751])).
% 2.08/0.63  fof(f1907,plain,(
% 2.08/0.63    v1_xboole_0(sK5(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_5)),
% 2.08/0.63    inference(forward_demodulation,[],[f1306,f120])).
% 2.08/0.63  fof(f1306,plain,(
% 2.08/0.63    v1_xboole_0(sK5(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) | ~spl6_5),
% 2.08/0.63    inference(resolution,[],[f594,f144])).
% 2.08/0.63  fof(f594,plain,(
% 2.08/0.63    ( ! [X8] : (~r2_hidden(X8,k5_partfun1(sK0,sK1,sK2)) | v1_xboole_0(X8)) ) | ~spl6_5),
% 2.08/0.63    inference(subsumption_resolution,[],[f224,f129])).
% 2.08/0.63  fof(f129,plain,(
% 2.08/0.63    v1_xboole_0(sK1) | ~spl6_5),
% 2.08/0.63    inference(avatar_component_clause,[],[f128])).
% 2.08/0.63  fof(f128,plain,(
% 2.08/0.63    spl6_5 <=> v1_xboole_0(sK1)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.08/0.63  fof(f224,plain,(
% 2.08/0.63    ( ! [X8] : (~r2_hidden(X8,k5_partfun1(sK0,sK1,sK2)) | v1_xboole_0(X8) | ~v1_xboole_0(sK1)) )),
% 2.08/0.63    inference(resolution,[],[f107,f69])).
% 2.08/0.63  fof(f69,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f24])).
% 2.08/0.63  fof(f24,plain,(
% 2.08/0.63    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f13])).
% 2.08/0.63  fof(f13,axiom,(
% 2.08/0.63    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.08/0.63  fof(f76,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f52])).
% 2.08/0.63  fof(f3019,plain,(
% 2.08/0.63    ( ! [X18] : (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X18)) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(subsumption_resolution,[],[f3018,f2051])).
% 2.08/0.63  fof(f2051,plain,(
% 2.08/0.63    v1_funct_1(k1_xboole_0) | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f56,f1751])).
% 2.08/0.63  fof(f3018,plain,(
% 2.08/0.63    ( ! [X18] : (~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X18) | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(forward_demodulation,[],[f3017,f2473])).
% 2.08/0.63  fof(f2473,plain,(
% 2.08/0.63    k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2460,f64])).
% 2.08/0.63  fof(f2460,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(subsumption_resolution,[],[f2458,f1763])).
% 2.08/0.63  fof(f2458,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)) | r2_hidden(X1,k1_xboole_0)) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2454,f74])).
% 2.08/0.63  fof(f2454,plain,(
% 2.08/0.63    r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2449,f77])).
% 2.08/0.63  fof(f2449,plain,(
% 2.08/0.63    m1_subset_1(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(subsumption_resolution,[],[f2447,f60])).
% 2.08/0.63  fof(f2447,plain,(
% 2.08/0.63    m1_subset_1(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2442,f66])).
% 2.08/0.63  fof(f66,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f46])).
% 2.08/0.63  fof(f2442,plain,(
% 2.08/0.63    r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f1792,f2024])).
% 2.08/0.63  fof(f2024,plain,(
% 2.08/0.63    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f2023,f1751])).
% 2.08/0.63  fof(f2023,plain,(
% 2.08/0.63    r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_3),
% 2.08/0.63    inference(forward_demodulation,[],[f2022,f92])).
% 2.08/0.63  fof(f2022,plain,(
% 2.08/0.63    r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_3),
% 2.08/0.63    inference(forward_demodulation,[],[f141,f120])).
% 2.08/0.63  fof(f141,plain,(
% 2.08/0.63    r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.08/0.63    inference(subsumption_resolution,[],[f103,f60])).
% 2.08/0.63  fof(f103,plain,(
% 2.08/0.63    r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.08/0.63    inference(resolution,[],[f57,f65])).
% 2.08/0.63  fof(f3017,plain,(
% 2.08/0.63    ( ! [X18] : (~v1_funct_1(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X18) | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(forward_demodulation,[],[f2979,f93])).
% 2.08/0.63  fof(f93,plain,(
% 2.08/0.63    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.08/0.63    inference(equality_resolution,[],[f80])).
% 2.08/0.63  fof(f80,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.08/0.63    inference(cnf_transformation,[],[f55])).
% 2.08/0.63  fof(f2979,plain,(
% 2.08/0.63    ( ! [X18] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X18) | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(forward_demodulation,[],[f2978,f2473])).
% 2.08/0.63  fof(f2978,plain,(
% 2.08/0.63    ( ! [X18] : (~v1_funct_2(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_xboole_0,X18) | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(forward_demodulation,[],[f2977,f93])).
% 2.08/0.63  fof(f2977,plain,(
% 2.08/0.63    ( ! [X18] : (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(forward_demodulation,[],[f2976,f2473])).
% 2.08/0.63  fof(f2976,plain,(
% 2.08/0.63    ( ! [X18] : (r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(forward_demodulation,[],[f2975,f93])).
% 2.08/0.63  fof(f2975,plain,(
% 2.08/0.63    ( ! [X18] : (r2_hidden(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39 | spl6_77)),
% 2.08/0.63    inference(subsumption_resolution,[],[f2974,f2845])).
% 2.08/0.63  fof(f2845,plain,(
% 2.08/0.63    k1_xboole_0 != k1_zfmisc_1(k1_xboole_0) | spl6_77),
% 2.08/0.63    inference(avatar_component_clause,[],[f2844])).
% 2.08/0.63  fof(f2974,plain,(
% 2.08/0.63    ( ! [X18] : (k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) | r2_hidden(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(forward_demodulation,[],[f2969,f93])).
% 2.08/0.63  fof(f2969,plain,(
% 2.08/0.63    ( ! [X18] : (k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)) | r2_hidden(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_funct_2(k1_xboole_0,X18)) | ~v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0),k1_xboole_0,X18) | ~v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)),k1_xboole_0))) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2959,f94])).
% 2.08/0.63  fof(f94,plain,(
% 2.08/0.63    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 2.08/0.63    inference(equality_resolution,[],[f84])).
% 2.08/0.63  fof(f84,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f31])).
% 2.08/0.63  fof(f31,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.08/0.63    inference(flattening,[],[f30])).
% 2.08/0.63  fof(f30,plain,(
% 2.08/0.63    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.08/0.63    inference(ennf_transformation,[],[f15])).
% 2.08/0.63  fof(f15,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).
% 2.08/0.63  fof(f2959,plain,(
% 2.08/0.63    ( ! [X0] : (m1_subset_1(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(duplicate_literal_removal,[],[f2952])).
% 2.08/0.63  fof(f2952,plain,(
% 2.08/0.63    ( ! [X0] : (m1_subset_1(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2542,f2543])).
% 2.08/0.63  fof(f2542,plain,(
% 2.08/0.63    ( ! [X1] : (v1_xboole_0(X1) | m1_subset_1(sK5(X1,k1_xboole_0),X1) | k1_xboole_0 = X1) ) | (~spl6_3 | ~spl6_9 | ~spl6_39)),
% 2.08/0.63    inference(resolution,[],[f2444,f66])).
% 2.08/0.63  fof(f2207,plain,(
% 2.08/0.63    ~spl6_3 | ~spl6_4 | spl6_43),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f2206])).
% 2.08/0.63  fof(f2206,plain,(
% 2.08/0.63    $false | (~spl6_3 | ~spl6_4 | spl6_43)),
% 2.08/0.63    inference(subsumption_resolution,[],[f2205,f126])).
% 2.08/0.63  fof(f126,plain,(
% 2.08/0.63    v1_xboole_0(sK0) | ~spl6_4),
% 2.08/0.63    inference(avatar_component_clause,[],[f124])).
% 2.08/0.63  fof(f124,plain,(
% 2.08/0.63    spl6_4 <=> v1_xboole_0(sK0)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.08/0.63  fof(f2205,plain,(
% 2.08/0.63    ~v1_xboole_0(sK0) | (~spl6_3 | spl6_43)),
% 2.08/0.63    inference(resolution,[],[f2170,f62])).
% 2.08/0.63  fof(f2170,plain,(
% 2.08/0.63    r2_hidden(sK5(sK0,k1_xboole_0),sK0) | (~spl6_3 | spl6_43)),
% 2.08/0.63    inference(resolution,[],[f2075,f75])).
% 2.08/0.63  fof(f2075,plain,(
% 2.08/0.63    ~r1_tarski(sK0,k1_xboole_0) | (~spl6_3 | spl6_43)),
% 2.08/0.63    inference(forward_demodulation,[],[f2074,f92])).
% 2.08/0.63  fof(f2074,plain,(
% 2.08/0.63    ~r1_tarski(sK0,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl6_3 | spl6_43)),
% 2.08/0.63    inference(forward_demodulation,[],[f1150,f120])).
% 2.08/0.63  fof(f1150,plain,(
% 2.08/0.63    ~r1_tarski(sK0,k2_zfmisc_1(sK0,sK1)) | spl6_43),
% 2.08/0.63    inference(avatar_component_clause,[],[f1149])).
% 2.08/0.63  fof(f1149,plain,(
% 2.08/0.63    spl6_43 <=> r1_tarski(sK0,k2_zfmisc_1(sK0,sK1))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 2.08/0.63  fof(f2078,plain,(
% 2.08/0.63    ~spl6_3 | ~spl6_9 | spl6_40),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f2077])).
% 2.08/0.63  fof(f2077,plain,(
% 2.08/0.63    $false | (~spl6_3 | ~spl6_9 | spl6_40)),
% 2.08/0.63    inference(subsumption_resolution,[],[f901,f1751])).
% 2.08/0.63  fof(f901,plain,(
% 2.08/0.63    k1_xboole_0 != sK2 | spl6_40),
% 2.08/0.63    inference(avatar_component_clause,[],[f900])).
% 2.08/0.63  fof(f900,plain,(
% 2.08/0.63    spl6_40 <=> k1_xboole_0 = sK2),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 2.08/0.63  fof(f1689,plain,(
% 2.08/0.63    ~spl6_9 | ~spl6_39 | ~spl6_40 | spl6_45),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f1688])).
% 2.08/0.63  fof(f1688,plain,(
% 2.08/0.63    $false | (~spl6_9 | ~spl6_39 | ~spl6_40 | spl6_45)),
% 2.08/0.63    inference(subsumption_resolution,[],[f1629,f1600])).
% 2.08/0.63  fof(f1600,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl6_39 | ~spl6_40)),
% 2.08/0.63    inference(forward_demodulation,[],[f869,f902])).
% 2.08/0.63  fof(f902,plain,(
% 2.08/0.63    k1_xboole_0 = sK2 | ~spl6_40),
% 2.08/0.63    inference(avatar_component_clause,[],[f900])).
% 2.08/0.63  fof(f1629,plain,(
% 2.08/0.63    r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0) | (~spl6_9 | ~spl6_40 | spl6_45)),
% 2.08/0.63    inference(backward_demodulation,[],[f1190,f1618])).
% 2.08/0.63  fof(f1618,plain,(
% 2.08/0.63    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl6_9 | ~spl6_40)),
% 2.08/0.63    inference(forward_demodulation,[],[f162,f902])).
% 2.08/0.63  fof(f1190,plain,(
% 2.08/0.63    r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),k2_zfmisc_1(sK0,sK1)) | spl6_45),
% 2.08/0.63    inference(resolution,[],[f1165,f75])).
% 2.08/0.63  fof(f1165,plain,(
% 2.08/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK0) | spl6_45),
% 2.08/0.63    inference(avatar_component_clause,[],[f1163])).
% 2.08/0.63  fof(f1163,plain,(
% 2.08/0.63    spl6_45 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK0)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.08/0.63  fof(f1488,plain,(
% 2.08/0.63    spl6_3 | spl6_20),
% 2.08/0.63    inference(avatar_split_clause,[],[f1487,f300,f118])).
% 2.08/0.63  fof(f300,plain,(
% 2.08/0.63    spl6_20 <=> ! [X6] : (~r2_hidden(X6,k5_partfun1(sK0,sK1,sK2)) | r2_hidden(X6,k1_funct_2(sK0,sK1)))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.08/0.63  fof(f1487,plain,(
% 2.08/0.63    ( ! [X6] : (~r2_hidden(X6,k5_partfun1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | r2_hidden(X6,k1_funct_2(sK0,sK1))) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f1486,f105])).
% 2.08/0.63  fof(f105,plain,(
% 2.08/0.63    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | v1_funct_1(X0)) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f95,f56])).
% 2.08/0.63  fof(f95,plain,(
% 2.08/0.63    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | v1_funct_1(X0) | ~v1_funct_1(sK2)) )),
% 2.08/0.63    inference(resolution,[],[f57,f85])).
% 2.08/0.63  fof(f85,plain,(
% 2.08/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f33])).
% 2.08/0.63  fof(f1486,plain,(
% 2.08/0.63    ( ! [X6] : (~r2_hidden(X6,k5_partfun1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | r2_hidden(X6,k1_funct_2(sK0,sK1)) | ~v1_funct_1(X6)) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f1262,f106])).
% 2.08/0.63  fof(f1262,plain,(
% 2.08/0.63    ( ! [X6] : (~r2_hidden(X6,k5_partfun1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | r2_hidden(X6,k1_funct_2(sK0,sK1)) | ~v1_funct_2(X6,sK0,sK1) | ~v1_funct_1(X6)) )),
% 2.08/0.63    inference(resolution,[],[f107,f83])).
% 2.08/0.63  fof(f83,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f31])).
% 2.08/0.63  fof(f1484,plain,(
% 2.08/0.63    ~spl6_10 | spl6_39),
% 2.08/0.63    inference(avatar_split_clause,[],[f1483,f868,f180])).
% 2.08/0.63  fof(f180,plain,(
% 2.08/0.63    spl6_10 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.08/0.63  fof(f1483,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 2.08/0.63    inference(global_subsumption,[],[f1303])).
% 2.08/0.63  fof(f1303,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 2.08/0.63    inference(resolution,[],[f153,f62])).
% 2.08/0.63  fof(f153,plain,(
% 2.08/0.63    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK2)) )),
% 2.08/0.63    inference(resolution,[],[f102,f74])).
% 2.08/0.63  fof(f1465,plain,(
% 2.08/0.63    ~spl6_8 | spl6_9),
% 2.08/0.63    inference(avatar_split_clause,[],[f892,f160,f156])).
% 2.08/0.63  fof(f156,plain,(
% 2.08/0.63    spl6_8 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.08/0.63  fof(f892,plain,(
% 2.08/0.63    sK2 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 2.08/0.63    inference(resolution,[],[f102,f73])).
% 2.08/0.63  fof(f73,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f48])).
% 2.08/0.63  fof(f48,plain,(
% 2.08/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.63    inference(flattening,[],[f47])).
% 2.08/0.63  fof(f47,plain,(
% 2.08/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.63    inference(nnf_transformation,[],[f5])).
% 2.08/0.63  fof(f5,axiom,(
% 2.08/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.08/0.63  fof(f1456,plain,(
% 2.08/0.63    ~spl6_20),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f1455])).
% 2.08/0.63  fof(f1455,plain,(
% 2.08/0.63    $false | ~spl6_20),
% 2.08/0.63    inference(subsumption_resolution,[],[f1452,f58])).
% 2.08/0.63  fof(f1452,plain,(
% 2.08/0.63    r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) | ~spl6_20),
% 2.08/0.63    inference(resolution,[],[f1327,f76])).
% 2.08/0.63  fof(f1327,plain,(
% 2.08/0.63    r2_hidden(sK5(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) | ~spl6_20),
% 2.08/0.63    inference(resolution,[],[f301,f144])).
% 2.08/0.63  fof(f301,plain,(
% 2.08/0.63    ( ! [X6] : (~r2_hidden(X6,k5_partfun1(sK0,sK1,sK2)) | r2_hidden(X6,k1_funct_2(sK0,sK1))) ) | ~spl6_20),
% 2.08/0.63    inference(avatar_component_clause,[],[f300])).
% 2.08/0.63  fof(f1170,plain,(
% 2.08/0.63    ~spl6_45 | spl6_46 | ~spl6_43),
% 2.08/0.63    inference(avatar_split_clause,[],[f1161,f1149,f1167,f1163])).
% 2.08/0.63  fof(f1161,plain,(
% 2.08/0.63    sK0 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK0) | ~spl6_43),
% 2.08/0.63    inference(resolution,[],[f1151,f73])).
% 2.08/0.63  fof(f1151,plain,(
% 2.08/0.63    r1_tarski(sK0,k2_zfmisc_1(sK0,sK1)) | ~spl6_43),
% 2.08/0.63    inference(avatar_component_clause,[],[f1149])).
% 2.08/0.63  fof(f592,plain,(
% 2.08/0.63    ~spl6_6),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f591])).
% 2.08/0.63  fof(f591,plain,(
% 2.08/0.63    $false | ~spl6_6),
% 2.08/0.63    inference(subsumption_resolution,[],[f242,f134])).
% 2.08/0.63  fof(f134,plain,(
% 2.08/0.63    v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) | ~spl6_6),
% 2.08/0.63    inference(avatar_component_clause,[],[f132])).
% 2.08/0.63  fof(f132,plain,(
% 2.08/0.63    spl6_6 <=> v1_xboole_0(k5_partfun1(sK0,sK1,sK2))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.08/0.63  fof(f578,plain,(
% 2.08/0.63    ~spl6_3 | ~spl6_9 | spl6_14),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f577])).
% 2.08/0.63  fof(f577,plain,(
% 2.08/0.63    $false | (~spl6_3 | ~spl6_9 | spl6_14)),
% 2.08/0.63    inference(subsumption_resolution,[],[f576,f492])).
% 2.08/0.63  fof(f492,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(backward_demodulation,[],[f437,f442])).
% 2.08/0.63  fof(f442,plain,(
% 2.08/0.63    k1_xboole_0 = sK2 | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f441,f92])).
% 2.08/0.63  fof(f441,plain,(
% 2.08/0.63    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl6_3 | ~spl6_9)),
% 2.08/0.63    inference(forward_demodulation,[],[f162,f120])).
% 2.08/0.63  fof(f437,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl6_3),
% 2.08/0.63    inference(subsumption_resolution,[],[f436,f59])).
% 2.08/0.63  fof(f59,plain,(
% 2.08/0.63    v1_xboole_0(k1_xboole_0)),
% 2.08/0.63    inference(cnf_transformation,[],[f3])).
% 2.08/0.63  fof(f3,axiom,(
% 2.08/0.63    v1_xboole_0(k1_xboole_0)),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.08/0.63  fof(f436,plain,(
% 2.08/0.63    ( ! [X1] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X1,sK2)) ) | ~spl6_3),
% 2.08/0.63    inference(forward_demodulation,[],[f435,f92])).
% 2.08/0.63  fof(f435,plain,(
% 2.08/0.63    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | ~r2_hidden(X1,sK2)) ) | ~spl6_3),
% 2.08/0.63    inference(forward_demodulation,[],[f217,f120])).
% 2.08/0.63  fof(f217,plain,(
% 2.08/0.63    ( ! [X1] : (~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 2.08/0.63    inference(resolution,[],[f153,f62])).
% 2.08/0.63  fof(f576,plain,(
% 2.08/0.63    r2_hidden(sK5(k1_xboole_0,sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))),k1_xboole_0) | (~spl6_3 | ~spl6_9 | spl6_14)),
% 2.08/0.63    inference(resolution,[],[f485,f75])).
% 2.08/0.63  fof(f485,plain,(
% 2.08/0.63    ~r1_tarski(k1_xboole_0,sK3(k5_partfun1(sK0,k1_xboole_0,k1_xboole_0))) | (~spl6_3 | ~spl6_9 | spl6_14)),
% 2.08/0.63    inference(backward_demodulation,[],[f407,f442])).
% 2.08/0.63  fof(f407,plain,(
% 2.08/0.63    ~r1_tarski(k1_xboole_0,sK3(k5_partfun1(sK0,k1_xboole_0,sK2))) | (~spl6_3 | spl6_14)),
% 2.08/0.63    inference(forward_demodulation,[],[f352,f92])).
% 2.08/0.63  fof(f352,plain,(
% 2.08/0.63    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3(k5_partfun1(sK0,k1_xboole_0,sK2))) | (~spl6_3 | spl6_14)),
% 2.08/0.63    inference(backward_demodulation,[],[f264,f120])).
% 2.08/0.63  fof(f264,plain,(
% 2.08/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k5_partfun1(sK0,sK1,sK2))) | spl6_14),
% 2.08/0.63    inference(avatar_component_clause,[],[f262])).
% 2.08/0.63  fof(f262,plain,(
% 2.08/0.63    spl6_14 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k5_partfun1(sK0,sK1,sK2)))),
% 2.08/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.08/0.63  fof(f430,plain,(
% 2.08/0.63    ~spl6_3 | spl6_8),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f429])).
% 2.08/0.63  fof(f429,plain,(
% 2.08/0.63    $false | (~spl6_3 | spl6_8)),
% 2.08/0.63    inference(subsumption_resolution,[],[f428,f59])).
% 2.08/0.63  fof(f428,plain,(
% 2.08/0.63    ~v1_xboole_0(k1_xboole_0) | (~spl6_3 | spl6_8)),
% 2.08/0.63    inference(forward_demodulation,[],[f427,f92])).
% 2.08/0.63  fof(f427,plain,(
% 2.08/0.63    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl6_3 | spl6_8)),
% 2.08/0.63    inference(forward_demodulation,[],[f256,f120])).
% 2.08/0.63  fof(f256,plain,(
% 2.08/0.63    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_8),
% 2.08/0.63    inference(resolution,[],[f174,f62])).
% 2.08/0.63  fof(f174,plain,(
% 2.08/0.63    r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(sK0,sK1)) | spl6_8),
% 2.08/0.63    inference(resolution,[],[f158,f75])).
% 2.08/0.63  fof(f158,plain,(
% 2.08/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl6_8),
% 2.08/0.63    inference(avatar_component_clause,[],[f156])).
% 2.08/0.63  fof(f376,plain,(
% 2.08/0.63    ~spl6_3 | spl6_10),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f375])).
% 2.08/0.63  fof(f375,plain,(
% 2.08/0.63    $false | (~spl6_3 | spl6_10)),
% 2.08/0.63    inference(subsumption_resolution,[],[f374,f59])).
% 2.08/0.63  fof(f374,plain,(
% 2.08/0.63    ~v1_xboole_0(k1_xboole_0) | (~spl6_3 | spl6_10)),
% 2.08/0.63    inference(forward_demodulation,[],[f324,f92])).
% 2.08/0.63  fof(f324,plain,(
% 2.08/0.63    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl6_3 | spl6_10)),
% 2.08/0.63    inference(backward_demodulation,[],[f182,f120])).
% 2.08/0.63  fof(f182,plain,(
% 2.08/0.63    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_10),
% 2.08/0.63    inference(avatar_component_clause,[],[f180])).
% 2.08/0.63  fof(f367,plain,(
% 2.08/0.63    ~spl6_3 | spl6_5),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f366])).
% 2.08/0.63  fof(f366,plain,(
% 2.08/0.63    $false | (~spl6_3 | spl6_5)),
% 2.08/0.63    inference(subsumption_resolution,[],[f312,f59])).
% 2.08/0.63  fof(f312,plain,(
% 2.08/0.63    ~v1_xboole_0(k1_xboole_0) | (~spl6_3 | spl6_5)),
% 2.08/0.63    inference(backward_demodulation,[],[f130,f120])).
% 2.08/0.63  fof(f130,plain,(
% 2.08/0.63    ~v1_xboole_0(sK1) | spl6_5),
% 2.08/0.63    inference(avatar_component_clause,[],[f128])).
% 2.08/0.63  fof(f269,plain,(
% 2.08/0.63    ~spl6_14 | spl6_15 | spl6_6),
% 2.08/0.63    inference(avatar_split_clause,[],[f260,f132,f266,f262])).
% 2.08/0.63  fof(f260,plain,(
% 2.08/0.63    k2_zfmisc_1(sK0,sK1) = sK3(k5_partfun1(sK0,sK1,sK2)) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k5_partfun1(sK0,sK1,sK2))) | spl6_6),
% 2.08/0.63    inference(resolution,[],[f251,f73])).
% 2.08/0.63  fof(f251,plain,(
% 2.08/0.63    r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK1)) | spl6_6),
% 2.08/0.63    inference(resolution,[],[f226,f173])).
% 2.08/0.63  fof(f173,plain,(
% 2.08/0.63    r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2)) | spl6_6),
% 2.08/0.63    inference(resolution,[],[f133,f63])).
% 2.08/0.63  fof(f133,plain,(
% 2.08/0.63    ~v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) | spl6_6),
% 2.08/0.63    inference(avatar_component_clause,[],[f132])).
% 2.08/0.63  fof(f226,plain,(
% 2.08/0.63    ( ! [X11] : (~r2_hidden(X11,k5_partfun1(sK0,sK1,sK2)) | r1_tarski(X11,k2_zfmisc_1(sK0,sK1))) )),
% 2.08/0.63    inference(resolution,[],[f107,f77])).
% 2.08/0.63  fof(f207,plain,(
% 2.08/0.63    spl6_6 | ~spl6_12),
% 2.08/0.63    inference(avatar_contradiction_clause,[],[f206])).
% 2.08/0.63  fof(f206,plain,(
% 2.08/0.63    $false | (spl6_6 | ~spl6_12)),
% 2.08/0.63    inference(subsumption_resolution,[],[f202,f59])).
% 2.08/0.63  fof(f202,plain,(
% 2.08/0.63    ~v1_xboole_0(k1_xboole_0) | (spl6_6 | ~spl6_12)),
% 2.08/0.63    inference(backward_demodulation,[],[f133,f192])).
% 2.08/0.63  fof(f192,plain,(
% 2.08/0.63    k1_xboole_0 = k5_partfun1(sK0,sK1,sK2) | ~spl6_12),
% 2.08/0.63    inference(avatar_component_clause,[],[f190])).
% 2.08/0.63  fof(f135,plain,(
% 2.08/0.63    spl6_4 | ~spl6_5 | spl6_6),
% 2.08/0.63    inference(avatar_split_clause,[],[f122,f132,f128,f124])).
% 2.08/0.63  fof(f122,plain,(
% 2.08/0.63    v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) | ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 2.08/0.63    inference(subsumption_resolution,[],[f99,f56])).
% 2.08/0.63  fof(f99,plain,(
% 2.08/0.63    v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) | ~v1_funct_1(sK2) | ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 2.08/0.63    inference(resolution,[],[f57,f82])).
% 2.08/0.63  fof(f82,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f29])).
% 2.08/0.63  fof(f29,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.08/0.63    inference(flattening,[],[f28])).
% 2.08/0.63  fof(f28,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.08/0.63    inference(ennf_transformation,[],[f14])).
% 2.08/0.63  fof(f14,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 2.08/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).
% 2.08/0.63  % SZS output end Proof for theBenchmark
% 2.08/0.63  % (16780)------------------------------
% 2.08/0.63  % (16780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (16780)Termination reason: Refutation
% 2.08/0.63  
% 2.08/0.63  % (16780)Memory used [KB]: 11641
% 2.08/0.63  % (16780)Time elapsed: 0.198 s
% 2.08/0.63  % (16780)------------------------------
% 2.08/0.63  % (16780)------------------------------
% 2.08/0.63  % (16770)Success in time 0.27 s
%------------------------------------------------------------------------------
