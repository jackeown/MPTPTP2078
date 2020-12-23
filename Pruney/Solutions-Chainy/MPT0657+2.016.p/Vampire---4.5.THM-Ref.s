%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 180 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  312 ( 636 expanded)
%              Number of equality atoms :   74 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f51,f55,f59,f93,f97,f118,f122,f127,f147,f167,f187,f203])).

fof(f203,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11
    | spl2_12
    | ~ spl2_17
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11
    | spl2_12
    | ~ spl2_17
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f201,f126])).

fof(f126,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_12
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f201,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f200,f146])).

fof(f146,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_17
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f200,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k4_relat_1(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f199,f186])).

fof(f186,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl2_26
  <=> k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f199,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f198,f166])).

fof(f166,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_22
  <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f198,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(resolution,[],[f183,f92])).

fof(f92,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(sK1,k5_relat_1(sK0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X1) )
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f181,f121])).

fof(f121,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_11
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f181,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(sK1,sK0),X1) = k5_relat_1(sK1,k5_relat_1(sK0,X1)) )
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f42,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f187,plain,
    ( spl2_26
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f110,f91,f53,f185])).

fof(f110,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f105,f83])).

fof(f83,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f105,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0))
    | ~ spl2_6 ),
    inference(resolution,[],[f92,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f167,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f79,f57,f53,f49,f165])).

fof(f49,plain,
    ( spl2_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( spl2_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f79,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f78,f25])).

fof(f25,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f78,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f77,f75])).

fof(f75,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f74,f54])).

fof(f74,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f67,f58])).

fof(f58,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f67,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f50,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f77,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f76,f54])).

fof(f76,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f68,f58])).

fof(f68,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f50,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f147,plain,
    ( spl2_17
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f62,f41,f145])).

fof(f62,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f127,plain,
    ( ~ spl2_12
    | spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f123,f116,f95,f125])).

fof(f95,plain,
    ( spl2_7
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f116,plain,
    ( spl2_10
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f123,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_7
    | ~ spl2_10 ),
    inference(superposition,[],[f96,f117])).

fof(f117,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f96,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f122,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f26,f120])).

fof(f26,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f118,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f75,f57,f53,f49,f116])).

fof(f97,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f27,f95])).

fof(f27,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f57,f53,f49,f91])).

fof(f71,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f70,f54])).

fof(f70,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f65,f58])).

fof(f65,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:01:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (17175)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (17183)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (17185)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (17185)Refutation not found, incomplete strategy% (17185)------------------------------
% 0.22/0.48  % (17185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17185)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (17185)Memory used [KB]: 6140
% 0.22/0.48  % (17185)Time elapsed: 0.049 s
% 0.22/0.48  % (17185)------------------------------
% 0.22/0.48  % (17185)------------------------------
% 0.22/0.48  % (17173)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (17179)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (17178)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (17173)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (17177)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (17184)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (17174)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (17187)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (17181)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (17188)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (17176)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (17182)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (17194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (17194)Refutation not found, incomplete strategy% (17194)------------------------------
% 0.22/0.50  % (17194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (17194)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (17194)Memory used [KB]: 10490
% 0.22/0.50  % (17194)Time elapsed: 0.099 s
% 0.22/0.50  % (17194)------------------------------
% 0.22/0.50  % (17194)------------------------------
% 0.22/0.50  % (17186)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (17189)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (17180)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (17192)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (17174)Refutation not found, incomplete strategy% (17174)------------------------------
% 0.22/0.51  % (17174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17174)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17174)Memory used [KB]: 10618
% 0.22/0.51  % (17174)Time elapsed: 0.091 s
% 0.22/0.51  % (17174)------------------------------
% 0.22/0.51  % (17174)------------------------------
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f43,f51,f55,f59,f93,f97,f118,f122,f127,f147,f167,f187,f203])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_11 | spl2_12 | ~spl2_17 | ~spl2_22 | ~spl2_26),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    $false | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_11 | spl2_12 | ~spl2_17 | ~spl2_22 | ~spl2_26)),
% 0.22/0.51    inference(subsumption_resolution,[],[f201,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    sK1 != k4_relat_1(sK0) | spl2_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl2_12 <=> sK1 = k4_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    sK1 = k4_relat_1(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_11 | ~spl2_17 | ~spl2_22 | ~spl2_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f200,f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f145])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl2_17 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k4_relat_1(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_11 | ~spl2_22 | ~spl2_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f199,f186])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) | ~spl2_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f185])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl2_26 <=> k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_11 | ~spl2_22)),
% 0.22/0.51    inference(forward_demodulation,[],[f198,f166])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~spl2_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl2_22 <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.22/0.51    inference(resolution,[],[f183,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v1_relat_1(k4_relat_1(sK0)) | ~spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl2_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(sK1,k5_relat_1(sK0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X1)) ) | (~spl2_1 | ~spl2_4 | ~spl2_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f181,f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) | ~spl2_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl2_11 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,sK0),X1) = k5_relat_1(sK1,k5_relat_1(sK0,X1))) ) | (~spl2_1 | ~spl2_4)),
% 0.22/0.51    inference(resolution,[],[f64,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl2_4 <=> v1_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1))) ) | ~spl2_1),
% 0.22/0.51    inference(resolution,[],[f42,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    spl2_26 | ~spl2_4 | ~spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f110,f91,f53,f185])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) | (~spl2_4 | ~spl2_6)),
% 0.22/0.51    inference(forward_demodulation,[],[f105,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl2_4),
% 0.22/0.51    inference(resolution,[],[f54,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0)) | ~spl2_6),
% 0.22/0.51    inference(resolution,[],[f92,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl2_22 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f79,f57,f53,f49,f165])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl2_3 <=> v2_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    spl2_5 <=> v1_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(forward_demodulation,[],[f78,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(forward_demodulation,[],[f77,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f54])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl2_3 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f67,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    v1_funct_1(sK0) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f57])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_3),
% 0.22/0.51    inference(resolution,[],[f50,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v2_funct_1(sK0) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f76,f54])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | (~spl2_3 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f58])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | ~spl2_3),
% 0.22/0.51    inference(resolution,[],[f50,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    spl2_17 | ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f41,f145])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_1),
% 0.22/0.51    inference(resolution,[],[f42,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ~spl2_12 | spl2_7 | ~spl2_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f123,f116,f95,f125])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl2_7 <=> sK1 = k2_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl2_10 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    sK1 != k4_relat_1(sK0) | (spl2_7 | ~spl2_10)),
% 0.22/0.51    inference(superposition,[],[f96,f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    sK1 != k2_funct_1(sK0) | spl2_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f95])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    spl2_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f120])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    spl2_10 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f75,f57,f53,f49,f116])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ~spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f95])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    sK1 != k2_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl2_6 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f71,f57,f53,f49,f91])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    v1_relat_1(k4_relat_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f54])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | v1_relat_1(k4_relat_1(sK0)) | (~spl2_3 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f65,f58])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | v1_relat_1(k4_relat_1(sK0)) | ~spl2_3),
% 0.22/0.51    inference(resolution,[],[f50,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f57])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    v1_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f53])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    v1_relat_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f49])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    v2_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f22,f41])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (17173)------------------------------
% 0.22/0.51  % (17173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17173)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (17173)Memory used [KB]: 6268
% 0.22/0.51  % (17173)Time elapsed: 0.077 s
% 0.22/0.51  % (17173)------------------------------
% 0.22/0.51  % (17173)------------------------------
% 0.22/0.51  % (17191)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (17170)Success in time 0.154 s
%------------------------------------------------------------------------------
