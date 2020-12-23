%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 200 expanded)
%              Number of leaves         :   25 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  337 ( 855 expanded)
%              Number of equality atoms :   90 ( 280 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f438,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f81,f85,f89,f131,f140,f174,f180,f419,f428,f437])).

fof(f437,plain,
    ( ~ spl2_6
    | ~ spl2_13
    | spl2_15
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f433,f425,f138,f123,f79])).

fof(f79,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f123,plain,
    ( spl2_13
  <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f138,plain,
    ( spl2_15
  <=> sK1 = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f425,plain,
    ( spl2_48
  <=> k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f433,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl2_48 ),
    inference(superposition,[],[f57,f426])).

fof(f426,plain,
    ( k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f425])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f428,plain,
    ( ~ spl2_8
    | spl2_48
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f422,f417,f425,f87])).

fof(f87,plain,
    ( spl2_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f417,plain,
    ( spl2_47
  <=> k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f422,plain,
    ( k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl2_47 ),
    inference(superposition,[],[f98,f418])).

fof(f418,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f417])).

fof(f98,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f44,f92])).

fof(f92,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f419,plain,
    ( spl2_47
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f415,f172,f87,f79,f63,f417])).

fof(f63,plain,
    ( spl2_2
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f172,plain,
    ( spl2_18
  <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f415,plain,
    ( k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f410,f64])).

fof(f64,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f410,plain,
    ( k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(resolution,[],[f402,f80])).

fof(f80,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f402,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | k5_relat_1(k5_relat_1(X4,sK0),k4_relat_1(sK0)) = k5_relat_1(X4,k6_relat_1(k2_relat_1(sK1))) )
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f400,f173])).

fof(f173,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f400,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | k5_relat_1(k5_relat_1(X4,sK0),k4_relat_1(sK0)) = k5_relat_1(X4,k5_relat_1(sK0,k4_relat_1(sK0))) )
    | ~ spl2_8 ),
    inference(resolution,[],[f332,f88])).

fof(f88,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f332,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(X6)
        | ~ v1_relat_1(X7)
        | k5_relat_1(k5_relat_1(X7,X6),k4_relat_1(sK0)) = k5_relat_1(X7,k5_relat_1(X6,k4_relat_1(sK0))) )
    | ~ spl2_8 ),
    inference(resolution,[],[f224,f88])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),k4_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k4_relat_1(X2))) ) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f180,plain,
    ( ~ spl2_8
    | spl2_13
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f179,f172,f87,f67,f123,f87])).

fof(f67,plain,
    ( spl2_3
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f179,plain,
    ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f178,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f178,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(k2_relat_1(sK1))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f175,f68])).

fof(f68,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f175,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(k2_relat_1(sK1))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(superposition,[],[f159,f173])).

fof(f159,plain,
    ( ! [X4] :
        ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k4_relat_1(X4))),k1_relat_1(X4))
        | ~ v1_relat_1(X4) )
    | ~ spl2_8 ),
    inference(resolution,[],[f155,f88])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(X0))),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(X0))),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f99,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k4_relat_1(X1))),k2_relat_1(k4_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f174,plain,
    ( ~ spl2_8
    | ~ spl2_7
    | spl2_18
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f170,f129,f71,f67,f172,f83,f87])).

fof(f83,plain,
    ( spl2_7
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f71,plain,
    ( spl2_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f129,plain,
    ( spl2_14
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f170,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f169,f68])).

fof(f169,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f168,f130])).

fof(f130,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f168,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f140,plain,
    ( ~ spl2_15
    | spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f134,f129,f59,f138])).

fof(f59,plain,
    ( spl2_1
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f134,plain,
    ( sK1 != k4_relat_1(sK0)
    | spl2_1
    | ~ spl2_14 ),
    inference(superposition,[],[f60,f130])).

fof(f60,plain,
    ( k2_funct_1(sK0) != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f131,plain,
    ( ~ spl2_8
    | ~ spl2_7
    | spl2_14
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f126,f71,f129,f83,f87])).

fof(f126,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f52,f72])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f89,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f85,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

% (13545)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (13533)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (13536)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (13535)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (13537)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (13550)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (13542)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f81,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f63])).

fof(f40,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f41,f59])).

fof(f41,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13539)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (13540)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (13541)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (13549)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (13548)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (13547)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (13539)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f438,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f81,f85,f89,f131,f140,f174,f180,f419,f428,f437])).
% 0.22/0.53  fof(f437,plain,(
% 0.22/0.53    ~spl2_6 | ~spl2_13 | spl2_15 | ~spl2_48),
% 0.22/0.53    inference(avatar_split_clause,[],[f433,f425,f138,f123,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl2_6 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl2_13 <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    spl2_15 <=> sK1 = k4_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    spl2_48 <=> k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.22/0.53  fof(f433,plain,(
% 0.22/0.53    sK1 = k4_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl2_48),
% 0.22/0.53    inference(superposition,[],[f57,f426])).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_48),
% 0.22/0.53    inference(avatar_component_clause,[],[f425])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    ~spl2_8 | spl2_48 | ~spl2_47),
% 0.22/0.53    inference(avatar_split_clause,[],[f422,f417,f425,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl2_8 <=> v1_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.53  fof(f417,plain,(
% 0.22/0.53    spl2_47 <=> k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(sK0) | ~spl2_47),
% 0.22/0.53    inference(superposition,[],[f98,f418])).
% 0.22/0.53  fof(f418,plain,(
% 0.22/0.53    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) | ~spl2_47),
% 0.22/0.53    inference(avatar_component_clause,[],[f417])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(global_subsumption,[],[f44,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(superposition,[],[f45,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    spl2_47 | ~spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f415,f172,f87,f79,f63,f417])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl2_2 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl2_18 <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) | (~spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_18)),
% 0.22/0.53    inference(forward_demodulation,[],[f410,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f410,plain,(
% 0.22/0.53    k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | (~spl2_6 | ~spl2_8 | ~spl2_18)),
% 0.22/0.53    inference(resolution,[],[f402,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    v1_relat_1(sK1) | ~spl2_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f402,plain,(
% 0.22/0.53    ( ! [X4] : (~v1_relat_1(X4) | k5_relat_1(k5_relat_1(X4,sK0),k4_relat_1(sK0)) = k5_relat_1(X4,k6_relat_1(k2_relat_1(sK1)))) ) | (~spl2_8 | ~spl2_18)),
% 0.22/0.53    inference(forward_demodulation,[],[f400,f173])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~spl2_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f172])).
% 0.22/0.53  fof(f400,plain,(
% 0.22/0.53    ( ! [X4] : (~v1_relat_1(X4) | k5_relat_1(k5_relat_1(X4,sK0),k4_relat_1(sK0)) = k5_relat_1(X4,k5_relat_1(sK0,k4_relat_1(sK0)))) ) | ~spl2_8),
% 0.22/0.53    inference(resolution,[],[f332,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    v1_relat_1(sK0) | ~spl2_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    ( ! [X6,X7] : (~v1_relat_1(X6) | ~v1_relat_1(X7) | k5_relat_1(k5_relat_1(X7,X6),k4_relat_1(sK0)) = k5_relat_1(X7,k5_relat_1(X6,k4_relat_1(sK0)))) ) | ~spl2_8),
% 0.22/0.53    inference(resolution,[],[f224,f88])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),k4_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k4_relat_1(X2)))) )),
% 0.22/0.53    inference(resolution,[],[f49,f44])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ~spl2_8 | spl2_13 | ~spl2_3 | ~spl2_8 | ~spl2_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f179,f172,f87,f67,f123,f87])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl2_3 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_8 | ~spl2_18)),
% 0.22/0.53    inference(forward_demodulation,[],[f178,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k6_relat_1(k2_relat_1(sK1))),k2_relat_1(sK1)) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_8 | ~spl2_18)),
% 0.22/0.53    inference(forward_demodulation,[],[f175,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k6_relat_1(k2_relat_1(sK1))),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_8 | ~spl2_18)),
% 0.22/0.53    inference(superposition,[],[f159,f173])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X4] : (r1_tarski(k2_relat_1(k5_relat_1(sK0,k4_relat_1(X4))),k1_relat_1(X4)) | ~v1_relat_1(X4)) ) | ~spl2_8),
% 0.22/0.53    inference(resolution,[],[f155,f88])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(X0))),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(X0))),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(superposition,[],[f99,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k4_relat_1(X1))),k2_relat_1(k4_relat_1(X1))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(resolution,[],[f48,f44])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ~spl2_8 | ~spl2_7 | spl2_18 | ~spl2_3 | ~spl2_4 | ~spl2_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f170,f129,f71,f67,f172,f83,f87])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl2_7 <=> v1_funct_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl2_4 <=> v2_funct_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl2_14 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_4 | ~spl2_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f169,f68])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_4 | ~spl2_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f168,f130])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl2_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f129])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.53    inference(resolution,[],[f55,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    v2_funct_1(sK0) | ~spl2_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ~spl2_15 | spl2_1 | ~spl2_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f134,f129,f59,f138])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl2_1 <=> k2_funct_1(sK0) = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    sK1 != k4_relat_1(sK0) | (spl2_1 | ~spl2_14)),
% 0.22/0.53    inference(superposition,[],[f60,f130])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k2_funct_1(sK0) != sK1 | spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f59])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~spl2_8 | ~spl2_7 | spl2_14 | ~spl2_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f126,f71,f129,f83,f87])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.53    inference(resolution,[],[f52,f72])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl2_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f87])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f32,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl2_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f83])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v1_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  % (13545)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (13533)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (13536)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (13535)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (13537)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.54  % (13550)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.54  % (13542)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl2_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f36,f79])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    spl2_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f71])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    v2_funct_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    spl2_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f67])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f63])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ~spl2_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f59])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    k2_funct_1(sK0) != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (13539)------------------------------
% 0.22/0.54  % (13539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13539)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (13539)Memory used [KB]: 11001
% 0.22/0.54  % (13539)Time elapsed: 0.080 s
% 0.22/0.54  % (13546)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.54  % (13539)------------------------------
% 0.22/0.54  % (13539)------------------------------
% 0.22/0.54  % (13532)Success in time 0.177 s
%------------------------------------------------------------------------------
