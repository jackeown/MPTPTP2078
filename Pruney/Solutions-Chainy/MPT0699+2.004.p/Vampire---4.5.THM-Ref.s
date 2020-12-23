%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 189 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  406 ( 580 expanded)
%              Number of equality atoms :   55 (  86 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f108,f253,f271])).

fof(f271,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f107,f259])).

fof(f259,plain,
    ( ! [X4] : k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f209,f232])).

fof(f232,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl3_9
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f209,plain,
    ( ! [X4] :
        ( k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4)
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f208,f53])).

fof(f53,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f208,plain,
    ( ! [X4] :
        ( k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),k1_relat_1(k6_relat_1(X4)))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f207,f176])).

fof(f176,plain,
    ( ! [X6] : k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6))) = k9_relat_1(sK1,X6)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f175,f134])).

fof(f134,plain,
    ( ! [X4] : k2_relat_1(k7_relat_1(sK1,X4)) = k9_relat_1(sK1,X4)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f133,f54])).

fof(f54,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f133,plain,
    ( ! [X4] : k9_relat_1(sK1,k2_relat_1(k6_relat_1(X4))) = k2_relat_1(k7_relat_1(sK1,X4))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f132,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f132,plain,
    ( ! [X4] :
        ( k9_relat_1(sK1,k2_relat_1(k6_relat_1(X4))) = k2_relat_1(k7_relat_1(sK1,X4))
        | ~ v1_relat_1(k6_relat_1(X4)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f123,f78])).

fof(f78,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f123,plain,
    ( ! [X4] :
        ( k9_relat_1(sK1,k2_relat_1(k6_relat_1(X4))) = k2_relat_1(k7_relat_1(sK1,X4))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X4)) )
    | ~ spl3_1 ),
    inference(superposition,[],[f55,f90])).

fof(f90,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f78,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f175,plain,
    ( ! [X6] : k2_relat_1(k7_relat_1(sK1,X6)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f174,f125])).

fof(f125,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f124,f51])).

fof(f124,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f119,f78])).

fof(f119,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_1 ),
    inference(superposition,[],[f74,f90])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f174,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X6))
        | k2_relat_1(k7_relat_1(sK1,X6)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6))) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f164,f129])).

fof(f129,plain,
    ( ! [X2] : v1_funct_1(k7_relat_1(sK1,X2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f128,f51])).

fof(f128,plain,
    ( ! [X2] :
        ( v1_funct_1(k7_relat_1(sK1,X2))
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f127,f83])).

fof(f83,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( ! [X2] :
        ( v1_funct_1(k7_relat_1(sK1,X2))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f126,f78])).

fof(f126,plain,
    ( ! [X2] :
        ( v1_funct_1(k7_relat_1(sK1,X2))
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f121,plain,
    ( ! [X2] :
        ( v1_funct_1(k7_relat_1(sK1,X2))
        | ~ v1_funct_1(k6_relat_1(X2))
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl3_1 ),
    inference(superposition,[],[f73,f90])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f164,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(k7_relat_1(sK1,X6))
        | ~ v1_relat_1(k7_relat_1(sK1,X6))
        | k2_relat_1(k7_relat_1(sK1,X6)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6))) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f139,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f139,plain,
    ( ! [X0] : v2_funct_1(k7_relat_1(sK1,X0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f138,f90])).

fof(f138,plain,
    ( ! [X0] : v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f137,f51])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f135,f52])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f99,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v2_funct_1(k5_relat_1(X1,sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f98,f83])).

fof(f98,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK1)
        | ~ v2_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v2_funct_1(k5_relat_1(X1,sK1)) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f93,f78])).

fof(f93,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v2_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v2_funct_1(k5_relat_1(X1,sK1)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

fof(f88,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f207,plain,
    ( ! [X4] :
        ( k10_relat_1(k2_funct_1(sK1),k1_relat_1(k6_relat_1(X4))) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X4)))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f202,f51])).

fof(f202,plain,
    ( ! [X4] :
        ( k10_relat_1(k2_funct_1(sK1),k1_relat_1(k6_relat_1(X4))) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X4)))
        | ~ v1_relat_1(k6_relat_1(X4))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f56,f149])).

fof(f149,plain,
    ( ! [X0] : k5_relat_1(k2_funct_1(sK1),k6_relat_1(X0)) = k2_funct_1(k7_relat_1(sK1,X0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f148,f90])).

fof(f148,plain,
    ( ! [X0] : k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k6_relat_1(X0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f147,f48])).

fof(f48,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f147,plain,
    ( ! [X0] : k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k6_relat_1(X0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f146,f51])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k6_relat_1(X0))) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f144,f52])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k6_relat_1(X0))) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f97,f50])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f96,f83])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK1)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f92,f78])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f107,plain,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_4
  <=> k9_relat_1(sK1,sK0) = k10_relat_1(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f253,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_9 ),
    inference(subsumption_resolution,[],[f251,f78])).

fof(f251,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_2
    | spl3_9 ),
    inference(subsumption_resolution,[],[f250,f83])).

fof(f250,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_9 ),
    inference(resolution,[],[f233,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f233,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f108,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f47,f105])).

fof(f47,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f89,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:32:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.51  % (5119)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.51  % (5143)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.51  % (5121)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (5127)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.52  % (5117)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (5137)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.53  % (5116)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (5129)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.53  % (5142)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.54  % (5131)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.54  % (5118)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (5120)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.54  % (5123)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.54  % (5145)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.55  % (5144)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (5124)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (5136)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % (5126)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.55  % (5132)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.55  % (5125)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.56  % (5134)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.56  % (5128)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.56  % (5133)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.56  % (5140)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (5122)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.56  % (5133)Refutation not found, incomplete strategy% (5133)------------------------------
% 1.37/0.56  % (5133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (5133)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (5133)Memory used [KB]: 10618
% 1.37/0.56  % (5133)Time elapsed: 0.147 s
% 1.37/0.56  % (5133)------------------------------
% 1.37/0.56  % (5133)------------------------------
% 1.37/0.56  % (5139)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.56  % (5135)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.57  % (5141)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.58  % (5130)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.58  % (5136)Refutation found. Thanks to Tanya!
% 1.37/0.58  % SZS status Theorem for theBenchmark
% 1.37/0.58  % SZS output start Proof for theBenchmark
% 1.37/0.58  fof(f280,plain,(
% 1.37/0.58    $false),
% 1.37/0.58    inference(avatar_sat_refutation,[],[f79,f84,f89,f108,f253,f271])).
% 1.37/0.58  fof(f271,plain,(
% 1.37/0.58    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_9),
% 1.37/0.58    inference(avatar_contradiction_clause,[],[f268])).
% 1.37/0.58  fof(f268,plain,(
% 1.37/0.58    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_9)),
% 1.37/0.58    inference(subsumption_resolution,[],[f107,f259])).
% 1.37/0.58  fof(f259,plain,(
% 1.37/0.58    ( ! [X4] : (k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4)) ) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_9)),
% 1.37/0.58    inference(subsumption_resolution,[],[f209,f232])).
% 1.37/0.58  fof(f232,plain,(
% 1.37/0.58    v1_relat_1(k2_funct_1(sK1)) | ~spl3_9),
% 1.37/0.58    inference(avatar_component_clause,[],[f231])).
% 1.37/0.58  fof(f231,plain,(
% 1.37/0.58    spl3_9 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.37/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.37/0.58  fof(f209,plain,(
% 1.37/0.58    ( ! [X4] : (k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),X4) | ~v1_relat_1(k2_funct_1(sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(forward_demodulation,[],[f208,f53])).
% 1.37/0.58  fof(f53,plain,(
% 1.37/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.58    inference(cnf_transformation,[],[f8])).
% 1.37/0.58  fof(f8,axiom,(
% 1.37/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.37/0.58  fof(f208,plain,(
% 1.37/0.58    ( ! [X4] : (k9_relat_1(sK1,X4) = k10_relat_1(k2_funct_1(sK1),k1_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k2_funct_1(sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(forward_demodulation,[],[f207,f176])).
% 1.37/0.58  fof(f176,plain,(
% 1.37/0.58    ( ! [X6] : (k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6))) = k9_relat_1(sK1,X6)) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(forward_demodulation,[],[f175,f134])).
% 1.37/0.58  fof(f134,plain,(
% 1.37/0.58    ( ! [X4] : (k2_relat_1(k7_relat_1(sK1,X4)) = k9_relat_1(sK1,X4)) ) | ~spl3_1),
% 1.37/0.58    inference(forward_demodulation,[],[f133,f54])).
% 1.37/0.58  fof(f54,plain,(
% 1.37/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.58    inference(cnf_transformation,[],[f8])).
% 1.37/0.58  fof(f133,plain,(
% 1.37/0.58    ( ! [X4] : (k9_relat_1(sK1,k2_relat_1(k6_relat_1(X4))) = k2_relat_1(k7_relat_1(sK1,X4))) ) | ~spl3_1),
% 1.37/0.58    inference(subsumption_resolution,[],[f132,f51])).
% 1.37/0.58  fof(f51,plain,(
% 1.37/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f12])).
% 1.37/0.58  fof(f12,axiom,(
% 1.37/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.37/0.58  fof(f132,plain,(
% 1.37/0.58    ( ! [X4] : (k9_relat_1(sK1,k2_relat_1(k6_relat_1(X4))) = k2_relat_1(k7_relat_1(sK1,X4)) | ~v1_relat_1(k6_relat_1(X4))) ) | ~spl3_1),
% 1.37/0.58    inference(subsumption_resolution,[],[f123,f78])).
% 1.37/0.58  fof(f78,plain,(
% 1.37/0.58    v1_relat_1(sK1) | ~spl3_1),
% 1.37/0.58    inference(avatar_component_clause,[],[f76])).
% 1.37/0.58  fof(f76,plain,(
% 1.37/0.58    spl3_1 <=> v1_relat_1(sK1)),
% 1.37/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.58  fof(f123,plain,(
% 1.37/0.58    ( ! [X4] : (k9_relat_1(sK1,k2_relat_1(k6_relat_1(X4))) = k2_relat_1(k7_relat_1(sK1,X4)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X4))) ) | ~spl3_1),
% 1.37/0.58    inference(superposition,[],[f55,f90])).
% 1.37/0.58  fof(f90,plain,(
% 1.37/0.58    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl3_1),
% 1.37/0.58    inference(resolution,[],[f78,f70])).
% 1.37/0.58  fof(f70,plain,(
% 1.37/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f38])).
% 1.37/0.58  fof(f38,plain,(
% 1.37/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.37/0.58    inference(ennf_transformation,[],[f9])).
% 1.37/0.58  fof(f9,axiom,(
% 1.37/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.37/0.58  fof(f55,plain,(
% 1.37/0.58    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f24])).
% 1.37/0.58  fof(f24,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(ennf_transformation,[],[f5])).
% 1.37/0.58  fof(f5,axiom,(
% 1.37/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.37/0.58  fof(f175,plain,(
% 1.37/0.58    ( ! [X6] : (k2_relat_1(k7_relat_1(sK1,X6)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f174,f125])).
% 1.37/0.58  fof(f125,plain,(
% 1.37/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_1),
% 1.37/0.58    inference(subsumption_resolution,[],[f124,f51])).
% 1.37/0.58  fof(f124,plain,(
% 1.37/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl3_1),
% 1.37/0.58    inference(subsumption_resolution,[],[f119,f78])).
% 1.37/0.58  fof(f119,plain,(
% 1.37/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl3_1),
% 1.37/0.58    inference(superposition,[],[f74,f90])).
% 1.37/0.58  fof(f74,plain,(
% 1.37/0.58    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f43])).
% 1.37/0.58  fof(f43,plain,(
% 1.37/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(flattening,[],[f42])).
% 1.37/0.58  fof(f42,plain,(
% 1.37/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f3])).
% 1.37/0.58  fof(f3,axiom,(
% 1.37/0.58    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.37/0.58  fof(f174,plain,(
% 1.37/0.58    ( ! [X6] : (~v1_relat_1(k7_relat_1(sK1,X6)) | k2_relat_1(k7_relat_1(sK1,X6)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f164,f129])).
% 1.37/0.58  fof(f129,plain,(
% 1.37/0.58    ( ! [X2] : (v1_funct_1(k7_relat_1(sK1,X2))) ) | (~spl3_1 | ~spl3_2)),
% 1.37/0.58    inference(subsumption_resolution,[],[f128,f51])).
% 1.37/0.58  fof(f128,plain,(
% 1.37/0.58    ( ! [X2] : (v1_funct_1(k7_relat_1(sK1,X2)) | ~v1_relat_1(k6_relat_1(X2))) ) | (~spl3_1 | ~spl3_2)),
% 1.37/0.58    inference(subsumption_resolution,[],[f127,f83])).
% 1.37/0.58  fof(f83,plain,(
% 1.37/0.58    v1_funct_1(sK1) | ~spl3_2),
% 1.37/0.58    inference(avatar_component_clause,[],[f81])).
% 1.37/0.58  fof(f81,plain,(
% 1.37/0.58    spl3_2 <=> v1_funct_1(sK1)),
% 1.37/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.58  fof(f127,plain,(
% 1.37/0.58    ( ! [X2] : (v1_funct_1(k7_relat_1(sK1,X2)) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(X2))) ) | ~spl3_1),
% 1.37/0.58    inference(subsumption_resolution,[],[f126,f78])).
% 1.37/0.58  fof(f126,plain,(
% 1.37/0.58    ( ! [X2] : (v1_funct_1(k7_relat_1(sK1,X2)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(X2))) ) | ~spl3_1),
% 1.37/0.58    inference(subsumption_resolution,[],[f121,f52])).
% 1.37/0.58  fof(f52,plain,(
% 1.37/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f12])).
% 1.37/0.58  fof(f121,plain,(
% 1.37/0.58    ( ! [X2] : (v1_funct_1(k7_relat_1(sK1,X2)) | ~v1_funct_1(k6_relat_1(X2)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(X2))) ) | ~spl3_1),
% 1.37/0.58    inference(superposition,[],[f73,f90])).
% 1.37/0.58  fof(f73,plain,(
% 1.37/0.58    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f41])).
% 1.37/0.58  fof(f41,plain,(
% 1.37/0.58    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(flattening,[],[f40])).
% 1.37/0.58  fof(f40,plain,(
% 1.37/0.58    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f11])).
% 1.37/0.58  fof(f11,axiom,(
% 1.37/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.37/0.58  fof(f164,plain,(
% 1.37/0.58    ( ! [X6] : (~v1_funct_1(k7_relat_1(sK1,X6)) | ~v1_relat_1(k7_relat_1(sK1,X6)) | k2_relat_1(k7_relat_1(sK1,X6)) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X6)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(resolution,[],[f139,f60])).
% 1.37/0.58  fof(f60,plain,(
% 1.37/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f31])).
% 1.37/0.58  fof(f31,plain,(
% 1.37/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(flattening,[],[f30])).
% 1.37/0.58  fof(f30,plain,(
% 1.37/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f16])).
% 1.37/0.58  fof(f16,axiom,(
% 1.37/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.37/0.58  fof(f139,plain,(
% 1.37/0.58    ( ! [X0] : (v2_funct_1(k7_relat_1(sK1,X0))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(forward_demodulation,[],[f138,f90])).
% 1.37/0.58  fof(f138,plain,(
% 1.37/0.58    ( ! [X0] : (v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f137,f51])).
% 1.37/0.58  fof(f137,plain,(
% 1.37/0.58    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f135,f52])).
% 1.37/0.58  fof(f135,plain,(
% 1.37/0.58    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(resolution,[],[f99,f50])).
% 1.37/0.58  fof(f50,plain,(
% 1.37/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f13,axiom,(
% 1.37/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.37/0.58  fof(f99,plain,(
% 1.37/0.58    ( ! [X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(k5_relat_1(X1,sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f98,f83])).
% 1.37/0.58  fof(f98,plain,(
% 1.37/0.58    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_1(sK1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(k5_relat_1(X1,sK1))) ) | (~spl3_1 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f93,f78])).
% 1.37/0.58  fof(f93,plain,(
% 1.37/0.58    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(k5_relat_1(X1,sK1))) ) | ~spl3_3),
% 1.37/0.58    inference(resolution,[],[f88,f62])).
% 1.37/0.58  fof(f62,plain,(
% 1.37/0.58    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k5_relat_1(X0,X1))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f33])).
% 1.37/0.58  fof(f33,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(flattening,[],[f32])).
% 1.37/0.58  fof(f32,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f15])).
% 1.37/0.58  fof(f15,axiom,(
% 1.37/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).
% 1.37/0.58  fof(f88,plain,(
% 1.37/0.58    v2_funct_1(sK1) | ~spl3_3),
% 1.37/0.58    inference(avatar_component_clause,[],[f86])).
% 1.37/0.58  fof(f86,plain,(
% 1.37/0.58    spl3_3 <=> v2_funct_1(sK1)),
% 1.37/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.37/0.58  fof(f207,plain,(
% 1.37/0.58    ( ! [X4] : (k10_relat_1(k2_funct_1(sK1),k1_relat_1(k6_relat_1(X4))) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X4))) | ~v1_relat_1(k2_funct_1(sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f202,f51])).
% 1.37/0.58  fof(f202,plain,(
% 1.37/0.58    ( ! [X4] : (k10_relat_1(k2_funct_1(sK1),k1_relat_1(k6_relat_1(X4))) = k1_relat_1(k2_funct_1(k7_relat_1(sK1,X4))) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k2_funct_1(sK1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(superposition,[],[f56,f149])).
% 1.37/0.58  fof(f149,plain,(
% 1.37/0.58    ( ! [X0] : (k5_relat_1(k2_funct_1(sK1),k6_relat_1(X0)) = k2_funct_1(k7_relat_1(sK1,X0))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(forward_demodulation,[],[f148,f90])).
% 1.37/0.58  fof(f148,plain,(
% 1.37/0.58    ( ! [X0] : (k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k6_relat_1(X0))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(forward_demodulation,[],[f147,f48])).
% 1.37/0.58  fof(f48,plain,(
% 1.37/0.58    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f18])).
% 1.37/0.58  fof(f18,axiom,(
% 1.37/0.58    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 1.37/0.58  fof(f147,plain,(
% 1.37/0.58    ( ! [X0] : (k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k6_relat_1(X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f146,f51])).
% 1.37/0.58  fof(f146,plain,(
% 1.37/0.58    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k6_relat_1(X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f144,f52])).
% 1.37/0.58  fof(f144,plain,(
% 1.37/0.58    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(k6_relat_1(X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(resolution,[],[f97,f50])).
% 1.37/0.58  fof(f97,plain,(
% 1.37/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f96,f83])).
% 1.37/0.58  fof(f96,plain,(
% 1.37/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_1(sK1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))) ) | (~spl3_1 | ~spl3_3)),
% 1.37/0.58    inference(subsumption_resolution,[],[f92,f78])).
% 1.37/0.58  fof(f92,plain,(
% 1.37/0.58    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k5_relat_1(X0,sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0))) ) | ~spl3_3),
% 1.37/0.58    inference(resolution,[],[f88,f63])).
% 1.37/0.58  fof(f63,plain,(
% 1.37/0.58    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f35])).
% 1.37/0.58  fof(f35,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(flattening,[],[f34])).
% 1.37/0.58  fof(f34,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f17])).
% 1.37/0.58  fof(f17,axiom,(
% 1.37/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 1.37/0.58  fof(f56,plain,(
% 1.37/0.58    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f25])).
% 1.37/0.58  fof(f25,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(ennf_transformation,[],[f6])).
% 1.37/0.58  fof(f6,axiom,(
% 1.37/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.37/0.58  fof(f107,plain,(
% 1.37/0.58    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) | spl3_4),
% 1.37/0.58    inference(avatar_component_clause,[],[f105])).
% 1.37/0.58  fof(f105,plain,(
% 1.37/0.58    spl3_4 <=> k9_relat_1(sK1,sK0) = k10_relat_1(k2_funct_1(sK1),sK0)),
% 1.37/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.37/0.58  fof(f253,plain,(
% 1.37/0.58    ~spl3_1 | ~spl3_2 | spl3_9),
% 1.37/0.58    inference(avatar_contradiction_clause,[],[f252])).
% 1.37/0.58  fof(f252,plain,(
% 1.37/0.58    $false | (~spl3_1 | ~spl3_2 | spl3_9)),
% 1.37/0.58    inference(subsumption_resolution,[],[f251,f78])).
% 1.37/0.58  fof(f251,plain,(
% 1.37/0.58    ~v1_relat_1(sK1) | (~spl3_2 | spl3_9)),
% 1.37/0.58    inference(subsumption_resolution,[],[f250,f83])).
% 1.37/0.58  fof(f250,plain,(
% 1.37/0.58    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_9),
% 1.37/0.58    inference(resolution,[],[f233,f58])).
% 1.37/0.58  fof(f58,plain,(
% 1.37/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f29])).
% 1.37/0.58  fof(f29,plain,(
% 1.37/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.58    inference(flattening,[],[f28])).
% 1.37/0.58  fof(f28,plain,(
% 1.37/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f10])).
% 1.37/0.58  fof(f10,axiom,(
% 1.37/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.37/0.58  fof(f233,plain,(
% 1.37/0.58    ~v1_relat_1(k2_funct_1(sK1)) | spl3_9),
% 1.37/0.58    inference(avatar_component_clause,[],[f231])).
% 1.37/0.58  fof(f108,plain,(
% 1.37/0.58    ~spl3_4),
% 1.37/0.58    inference(avatar_split_clause,[],[f47,f105])).
% 1.37/0.58  fof(f47,plain,(
% 1.37/0.58    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)),
% 1.37/0.58    inference(cnf_transformation,[],[f23])).
% 1.37/0.58  fof(f23,plain,(
% 1.37/0.58    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.37/0.58    inference(flattening,[],[f22])).
% 1.37/0.58  fof(f22,plain,(
% 1.37/0.58    ? [X0,X1] : ((k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.37/0.58    inference(ennf_transformation,[],[f20])).
% 1.37/0.58  fof(f20,negated_conjecture,(
% 1.37/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.37/0.58    inference(negated_conjecture,[],[f19])).
% 1.37/0.58  fof(f19,conjecture,(
% 1.37/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.37/0.58  fof(f89,plain,(
% 1.37/0.58    spl3_3),
% 1.37/0.58    inference(avatar_split_clause,[],[f46,f86])).
% 1.37/0.58  fof(f46,plain,(
% 1.37/0.58    v2_funct_1(sK1)),
% 1.37/0.58    inference(cnf_transformation,[],[f23])).
% 1.37/0.58  fof(f84,plain,(
% 1.37/0.58    spl3_2),
% 1.37/0.58    inference(avatar_split_clause,[],[f45,f81])).
% 1.37/0.58  fof(f45,plain,(
% 1.37/0.58    v1_funct_1(sK1)),
% 1.37/0.58    inference(cnf_transformation,[],[f23])).
% 1.37/0.58  fof(f79,plain,(
% 1.37/0.58    spl3_1),
% 1.37/0.58    inference(avatar_split_clause,[],[f44,f76])).
% 1.37/0.58  fof(f44,plain,(
% 1.37/0.58    v1_relat_1(sK1)),
% 1.37/0.58    inference(cnf_transformation,[],[f23])).
% 1.37/0.58  % SZS output end Proof for theBenchmark
% 1.37/0.58  % (5136)------------------------------
% 1.37/0.58  % (5136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (5136)Termination reason: Refutation
% 1.37/0.58  
% 1.37/0.58  % (5136)Memory used [KB]: 11001
% 1.37/0.58  % (5136)Time elapsed: 0.145 s
% 1.37/0.58  % (5136)------------------------------
% 1.37/0.58  % (5136)------------------------------
% 1.37/0.58  % (5115)Success in time 0.213 s
%------------------------------------------------------------------------------
