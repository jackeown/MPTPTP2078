%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0680+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:26 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 252 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 ( 859 expanded)
%              Number of equality atoms :   79 ( 234 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f649,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f98,f109,f114,f241,f256,f273,f540,f640])).

fof(f640,plain,
    ( ~ spl4_1
    | ~ spl4_16
    | ~ spl4_18
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_16
    | ~ spl4_18
    | spl4_35 ),
    inference(subsumption_resolution,[],[f638,f612])).

fof(f612,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl4_1
    | spl4_35 ),
    inference(superposition,[],[f539,f349])).

fof(f349,plain,
    ( ! [X0,X1] : k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))
    | ~ spl4_1 ),
    inference(superposition,[],[f82,f80])).

fof(f80,plain,
    ( ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f63,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f82,plain,
    ( ! [X0,X1] : k9_relat_1(sK0,k4_xboole_0(X1,k1_tarski(X0))) = k4_xboole_0(k9_relat_1(sK0,X1),k11_relat_1(sK0,X0))
    | ~ spl4_1 ),
    inference(superposition,[],[f57,f80])).

fof(f57,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(definition_unfolding,[],[f38,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f38,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_funct_1(sK0)
    & ! [X1,X2] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ! [X2,X1] : k9_relat_1(sK0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_funct_1)).

fof(f539,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl4_35
  <=> k11_relat_1(sK0,sK1(sK0)) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f638,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl4_1
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f623,f80])).

fof(f623,plain,
    ( k9_relat_1(sK0,k1_tarski(sK1(sK0))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl4_1
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(superposition,[],[f359,f272])).

fof(f272,plain,
    ( k1_tarski(sK1(sK0)) = k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl4_18
  <=> k1_tarski(sK1(sK0)) = k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f359,plain,
    ( ! [X0] : k9_relat_1(sK0,k4_xboole_0(X0,k1_tarski(sK2(sK0)))) = k9_relat_1(sK0,k4_xboole_0(X0,k1_tarski(sK1(sK0))))
    | ~ spl4_1
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f350,f82])).

fof(f350,plain,
    ( ! [X0] : k9_relat_1(sK0,k4_xboole_0(X0,k1_tarski(sK2(sK0)))) = k4_xboole_0(k9_relat_1(sK0,X0),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl4_1
    | ~ spl4_16 ),
    inference(superposition,[],[f82,f240])).

fof(f240,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_16
  <=> k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f540,plain,
    ( ~ spl4_35
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f261,f253,f537])).

fof(f253,plain,
    ( spl4_17
  <=> k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f261,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl4_17 ),
    inference(superposition,[],[f59,f255])).

fof(f255,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f253])).

fof(f59,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f273,plain,
    ( spl4_18
    | spl4_6 ),
    inference(avatar_split_clause,[],[f129,f111,f270])).

fof(f111,plain,
    ( spl4_6
  <=> sK1(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f129,plain,
    ( k1_tarski(sK1(sK0)) = k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f113,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,
    ( sK1(sK0) != sK2(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f256,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f115,f95,f66,f61,f253])).

fof(f66,plain,
    ( spl4_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,
    ( spl4_4
  <=> r2_hidden(sK1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f115,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f63,f68,f97,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f97,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f68,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f241,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f128,f106,f95,f71,f66,f61,f238])).

fof(f71,plain,
    ( spl4_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f106,plain,
    ( spl4_5
  <=> r2_hidden(sK2(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f127,f115])).

fof(f127,plain,
    ( k1_tarski(k1_funct_1(sK0,sK1(sK0))) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f121,f99])).

fof(f99,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f63,f68,f73,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f73,plain,
    ( ~ v2_funct_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f121,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f63,f68,f108,f53])).

fof(f108,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f114,plain,
    ( ~ spl4_6
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f88,f71,f66,f61,f111])).

fof(f88,plain,
    ( sK1(sK0) != sK2(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f63,f68,f73,f46])).

fof(f46,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f109,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f86,f71,f66,f61,f106])).

fof(f86,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f63,f68,f73,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,
    ( spl4_4
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f84,f71,f66,f61,f95])).

fof(f84,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f63,f68,f73,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
