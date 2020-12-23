%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 496 expanded)
%              Number of leaves         :   31 ( 178 expanded)
%              Depth                    :   10
%              Number of atoms          :  486 (1349 expanded)
%              Number of equality atoms :  161 ( 601 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f117,f144,f157,f192,f199,f227,f239,f245,f248,f303,f320,f329,f338,f365,f403])).

fof(f403,plain,
    ( ~ spl5_1
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f72,f397])).

fof(f397,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(resolution,[],[f389,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,o_0_0_xboole_0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f45,f45])).

fof(f45,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f389,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f379,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),o_0_0_xboole_0,X3) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f66,f45,f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f379,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0,sK3))
    | ~ spl5_1
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f96,f172])).

fof(f172,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_11
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f96,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_1
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f72,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != sK0
    & ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
      | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
      | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
      | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
          | r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
          | r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
          | r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) ) )
   => ( k1_xboole_0 != sK0
      & ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
        | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
        | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
        | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
        | r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
        | r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
        | r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ ( ~ r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
            & ~ r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
            & ~ r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
            & ~ r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
          & ~ r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
          & ~ r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
          & ~ r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_mcart_1)).

fof(f365,plain,
    ( ~ spl5_20
    | spl5_7
    | spl5_5
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f363,f336,f125,f132,f327])).

fof(f327,plain,
    ( spl5_20
  <=> m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f132,plain,
    ( spl5_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f125,plain,
    ( spl5_5
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f336,plain,
    ( spl5_22
  <=> sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f363,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl5_22 ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | sK4(sK0) != sK4(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl5_22 ),
    inference(resolution,[],[f357,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) ) ),
    inference(definition_unfolding,[],[f70,f62])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),X0)
        | o_0_0_xboole_0 = X0
        | v1_xboole_0(X0)
        | sK4(X0) != sK4(sK0) )
    | ~ spl5_22 ),
    inference(resolution,[],[f353,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f353,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),X4)
        | sK4(sK0) != sK4(X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl5_22 ),
    inference(superposition,[],[f77,f337])).

fof(f337,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f336])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5)
      | ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f61,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f338,plain,
    ( spl5_5
    | spl5_10
    | spl5_11
    | spl5_9
    | spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f334,f327,f336,f165,f171,f168,f125])).

fof(f168,plain,
    ( spl5_10
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f165,plain,
    ( spl5_9
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f334,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)))
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | ~ spl5_20 ),
    inference(resolution,[],[f328,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f68,f71,f62,f45,f45,f45,f45])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f328,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f327])).

fof(f329,plain,
    ( spl5_5
    | spl5_20
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f324,f95,f327,f125])).

fof(f324,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(resolution,[],[f322,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(X0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f321,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f321,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)))
    | ~ spl5_1 ),
    inference(resolution,[],[f96,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f320,plain,
    ( ~ spl5_1
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f72,f315])).

fof(f315,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f314,f75])).

fof(f314,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f313,f92])).

fof(f92,plain,(
    ! [X2,X0,X3] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,o_0_0_xboole_0),X2,X3) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f65,f45,f45,f62])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f313,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK2,sK3))
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f96,f169])).

fof(f169,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f303,plain,
    ( ~ spl5_6
    | spl5_7
    | spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f302,f174,f125,f132,f128])).

fof(f128,plain,
    ( spl5_6
  <=> m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f174,plain,
    ( spl5_12
  <=> sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f302,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f300])).

fof(f300,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | sK4(sK0) != sK4(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl5_12 ),
    inference(resolution,[],[f260,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) ) ),
    inference(definition_unfolding,[],[f69,f62])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

% (4643)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),X0)
        | o_0_0_xboole_0 = X0
        | v1_xboole_0(X0)
        | sK4(X0) != sK4(sK0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f256,f52])).

fof(f256,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),X5)
        | sK4(sK0) != sK4(X5)
        | o_0_0_xboole_0 = X5 )
    | ~ spl5_12 ),
    inference(superposition,[],[f76,f175])).

fof(f175,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f174])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5)
      | ~ r2_hidden(X3,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f71,f45])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f248,plain,
    ( spl5_9
    | spl5_5
    | spl5_10
    | spl5_11
    | spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f247,f128,f174,f171,f168,f125,f165])).

fof(f247,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)))
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK3
    | ~ spl5_6 ),
    inference(resolution,[],[f129,f87])).

fof(f129,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f245,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f243,f104,f128,f125])).

fof(f104,plain,
    ( spl5_4
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f243,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | o_0_0_xboole_0 = sK0
    | ~ spl5_4 ),
    inference(resolution,[],[f201,f78])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(X0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f200,f57])).

fof(f200,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)))
    | ~ spl5_4 ),
    inference(resolution,[],[f105,f54])).

fof(f105,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f239,plain,
    ( ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f72,f235])).

fof(f235,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f234,f75])).

fof(f234,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f232,f91])).

fof(f232,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f105,f169])).

fof(f227,plain,
    ( ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f72,f223])).

fof(f223,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(resolution,[],[f222,f75])).

fof(f222,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f217,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X3
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f67,f45,f45,f62])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f217,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,o_0_0_xboole_0))
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f105,f172])).

fof(f199,plain,
    ( ~ spl5_1
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f72,f195])).

fof(f195,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f194,f75])).

fof(f194,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f193,f90])).

fof(f193,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,o_0_0_xboole_0))
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f96,f166])).

fof(f166,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f192,plain,
    ( ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f72,f188])).

fof(f188,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f187,f75])).

fof(f187,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f183,f93])).

fof(f93,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2,X3) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f64,f45,f45,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f183,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0),sK1,sK2))
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f105,f166])).

fof(f157,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f72,f138])).

fof(f138,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f133,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f144,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f72,f126])).

fof(f126,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f117,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f72,f113])).

fof(f113,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(resolution,[],[f102,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f102,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f111,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f72,f107])).

fof(f107,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(resolution,[],[f99,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_2
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f73,f104,f101,f98,f95])).

fof(f73,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    inference(definition_unfolding,[],[f42,f62,f62,f62,f62])).

fof(f42,plain,
    ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
    | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
    | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
    | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

%------------------------------------------------------------------------------
