%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t47_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 327 expanded)
%              Number of leaves         :   30 ( 134 expanded)
%              Depth                    :   15
%              Number of atoms          :  621 (1477 expanded)
%              Number of equality atoms :   87 ( 198 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f101,f108,f115,f122,f136,f143,f201,f208,f280,f296,f440,f507,f600,f628,f833,f898,f2153,f2193,f2206])).

fof(f2206,plain,
    ( ~ spl6_4
    | ~ spl6_6
    | spl6_9
    | ~ spl6_332 ),
    inference(avatar_contradiction_clause,[],[f2205])).

fof(f2205,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_332 ),
    inference(subsumption_resolution,[],[f2204,f107])).

fof(f107,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2204,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_332 ),
    inference(subsumption_resolution,[],[f2203,f114])).

fof(f114,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2203,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_9
    | ~ spl6_332 ),
    inference(subsumption_resolution,[],[f2201,f121])).

fof(f121,plain,
    ( ~ v2_funct_1(sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_9
  <=> ~ v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2201,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_332 ),
    inference(trivial_inequality_removal,[],[f2200])).

fof(f2200,plain,
    ( sK2(sK1) != sK2(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_332 ),
    inference(superposition,[],[f71,f2192])).

fof(f2192,plain,
    ( sK2(sK1) = sK3(sK1)
    | ~ spl6_332 ),
    inference(avatar_component_clause,[],[f2191])).

fof(f2191,plain,
    ( spl6_332
  <=> sK2(sK1) = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_332])])).

fof(f71,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t47_funct_1.p',d8_funct_1)).

fof(f2193,plain,
    ( spl6_332
    | ~ spl6_26
    | ~ spl6_154
    | ~ spl6_326 ),
    inference(avatar_split_clause,[],[f2171,f2149,f896,f206,f2191])).

fof(f206,plain,
    ( spl6_26
  <=> r2_hidden(sK3(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f896,plain,
    ( spl6_154
  <=> k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).

fof(f2149,plain,
    ( spl6_326
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_326])])).

fof(f2171,plain,
    ( sK2(sK1) = sK3(sK1)
    | ~ spl6_26
    | ~ spl6_154
    | ~ spl6_326 ),
    inference(subsumption_resolution,[],[f2168,f897])).

fof(f897,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ spl6_154 ),
    inference(avatar_component_clause,[],[f896])).

fof(f2168,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | sK2(sK1) = sK3(sK1)
    | ~ spl6_26
    | ~ spl6_326 ),
    inference(resolution,[],[f2150,f207])).

fof(f207,plain,
    ( r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f206])).

fof(f2150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X0 )
    | ~ spl6_326 ),
    inference(avatar_component_clause,[],[f2149])).

fof(f2153,plain,
    ( spl6_326
    | ~ spl6_12
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_136 ),
    inference(avatar_split_clause,[],[f919,f831,f612,f586,f278,f199,f134,f2149])).

fof(f134,plain,
    ( spl6_12
  <=> v2_funct_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f199,plain,
    ( spl6_24
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f278,plain,
    ( spl6_38
  <=> k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f586,plain,
    ( spl6_100
  <=> v1_relat_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f612,plain,
    ( spl6_104
  <=> v1_funct_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f831,plain,
    ( spl6_136
  <=> k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f919,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1 )
    | ~ spl6_12
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f918,f200])).

fof(f200,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f199])).

fof(f918,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1 )
    | ~ spl6_12
    | ~ spl6_38
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_136 ),
    inference(forward_demodulation,[],[f917,f279])).

fof(f279,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f278])).

fof(f917,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1
        | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl6_12
    | ~ spl6_38
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_136 ),
    inference(forward_demodulation,[],[f916,f279])).

fof(f916,plain,
    ( ! [X1] :
        ( k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0))) )
    | ~ spl6_12
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f915,f587])).

fof(f587,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f586])).

fof(f915,plain,
    ( ! [X1] :
        ( k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ v1_relat_1(k5_relat_1(sK1,sK0)) )
    | ~ spl6_12
    | ~ spl6_104
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f914,f613])).

fof(f613,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f612])).

fof(f914,plain,
    ( ! [X1] :
        ( k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ v1_funct_1(k5_relat_1(sK1,sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,sK0)) )
    | ~ spl6_12
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f907,f135])).

fof(f135,plain,
    ( v2_funct_1(k5_relat_1(sK1,sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f907,plain,
    ( ! [X1] :
        ( k1_funct_1(k5_relat_1(sK1,sK0),X1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
        | sK2(sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ v2_funct_1(k5_relat_1(sK1,sK0))
        | ~ v1_funct_1(k5_relat_1(sK1,sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,sK0)) )
    | ~ spl6_136 ),
    inference(superposition,[],[f67,f832])).

fof(f832,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ spl6_136 ),
    inference(avatar_component_clause,[],[f831])).

fof(f67,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f898,plain,
    ( spl6_154
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f573,f505,f99,f92,f896])).

fof(f92,plain,
    ( spl6_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f99,plain,
    ( spl6_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f505,plain,
    ( spl6_96
  <=> ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X0),sK3(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f573,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f570,f93])).

fof(f93,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f92])).

fof(f570,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_96 ),
    inference(resolution,[],[f506,f100])).

fof(f100,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X0),sK3(sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f505])).

fof(f833,plain,
    ( spl6_136
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f498,f438,f99,f92,f831])).

fof(f438,plain,
    ( spl6_76
  <=> ! [X2] :
        ( k1_funct_1(X2,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X2),sK2(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f498,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f495,f93])).

fof(f495,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_76 ),
    inference(resolution,[],[f439,f100])).

fof(f439,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(X2)
        | k1_funct_1(X2,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X2),sK2(sK1))
        | ~ v1_relat_1(X2) )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f438])).

fof(f628,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | spl6_105 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_105 ),
    inference(subsumption_resolution,[],[f626,f107])).

fof(f626,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_105 ),
    inference(subsumption_resolution,[],[f625,f114])).

fof(f625,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_105 ),
    inference(subsumption_resolution,[],[f624,f93])).

fof(f624,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_2
    | ~ spl6_105 ),
    inference(subsumption_resolution,[],[f622,f100])).

fof(f622,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_105 ),
    inference(resolution,[],[f616,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t47_funct_1.p',fc2_funct_1)).

fof(f616,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ spl6_105 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl6_105
  <=> ~ v1_funct_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f600,plain,
    ( ~ spl6_0
    | ~ spl6_4
    | spl6_101 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f598,f107])).

fof(f598,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_0
    | ~ spl6_101 ),
    inference(subsumption_resolution,[],[f596,f93])).

fof(f596,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl6_101 ),
    inference(resolution,[],[f590,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t47_funct_1.p',dt_k5_relat_1)).

fof(f590,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ spl6_101 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl6_101
  <=> ~ v1_relat_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f507,plain,
    ( spl6_96
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f443,f294,f206,f113,f106,f505])).

fof(f294,plain,
    ( spl6_42
  <=> k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f443,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X0),sK3(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f238,f295])).

fof(f295,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f294])).

fof(f238,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK3(sK1))) = k1_funct_1(k5_relat_1(sK1,X0),sK3(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f237,f107])).

fof(f237,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK3(sK1))) = k1_funct_1(k5_relat_1(sK1,X0),sK3(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f233,f114])).

fof(f233,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,k1_funct_1(sK1,sK3(sK1))) = k1_funct_1(k5_relat_1(sK1,X0),sK3(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_26 ),
    inference(resolution,[],[f207,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t47_funct_1.p',t23_funct_1)).

fof(f440,plain,
    ( spl6_76
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f232,f199,f113,f106,f438])).

fof(f232,plain,
    ( ! [X2] :
        ( k1_funct_1(X2,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X2),sK2(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f231,f107])).

fof(f231,plain,
    ( ! [X2] :
        ( k1_funct_1(X2,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X2),sK2(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f230,f114])).

fof(f230,plain,
    ( ! [X2] :
        ( k1_funct_1(X2,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,X2),sK2(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_24 ),
    inference(resolution,[],[f78,f200])).

fof(f296,plain,
    ( spl6_42
    | ~ spl6_4
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f218,f120,f113,f106,f294])).

fof(f218,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f217,f107])).

fof(f217,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f216,f114])).

fof(f216,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f70,f121])).

fof(f70,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f280,plain,
    ( spl6_38
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f228,f141,f106,f92,f278])).

fof(f141,plain,
    ( spl6_14
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f228,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f227,f107])).

fof(f227,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl6_0
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f226,f93])).

fof(f226,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl6_14 ),
    inference(resolution,[],[f66,f142])).

fof(f142,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t47_funct_1.p',t46_relat_1)).

fof(f208,plain,
    ( spl6_26
    | ~ spl6_4
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f193,f120,f113,f106,f206])).

fof(f193,plain,
    ( r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f192,f107])).

fof(f192,plain,
    ( r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f190,f121])).

fof(f190,plain,
    ( r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f69,f114])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f201,plain,
    ( spl6_24
    | ~ spl6_4
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_split_clause,[],[f181,f120,f113,f106,f199])).

fof(f181,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f180,f107])).

fof(f180,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f178,f121])).

fof(f178,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f68,f114])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f143,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    & v2_funct_1(k5_relat_1(sK1,sK0))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
            & v2_funct_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
          & v2_funct_1(k5_relat_1(X1,sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_funct_1(sK1)
        & r1_tarski(k2_relat_1(sK1),k1_relat_1(X0))
        & v2_funct_1(k5_relat_1(sK1,X0))
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => v2_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t47_funct_1.p',t47_funct_1)).

fof(f136,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f61,f134])).

fof(f61,plain,(
    v2_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f63,f120])).

fof(f63,plain,(
    ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f115,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f60,f113])).

fof(f60,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f59,f106])).

fof(f59,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f58,f99])).

fof(f58,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f57,f92])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
