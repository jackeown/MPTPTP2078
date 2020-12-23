%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t46_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 4.81s
% Output     : Refutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 460 expanded)
%              Number of leaves         :   39 ( 179 expanded)
%              Depth                    :   13
%              Number of atoms          :  874 (2175 expanded)
%              Number of equality atoms :   86 ( 288 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f90,f97,f104,f111,f118,f132,f174,f210,f222,f286,f292,f300,f469,f731,f769,f799,f863,f992,f6497,f6506,f7088,f24765,f24774,f94298,f95364,f95378])).

fof(f95378,plain,
    ( spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_7164 ),
    inference(avatar_contradiction_clause,[],[f95377])).

fof(f95377,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_7164 ),
    inference(subsumption_resolution,[],[f95376,f270])).

fof(f270,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl5_40
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f95376,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_42
    | ~ spl5_7164 ),
    inference(subsumption_resolution,[],[f95375,f276])).

fof(f276,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl5_42
  <=> v1_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f95375,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_7164 ),
    inference(subsumption_resolution,[],[f95373,f131])).

fof(f131,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_15
  <=> ~ v2_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f95373,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_7164 ),
    inference(trivial_inequality_removal,[],[f95371])).

fof(f95371,plain,
    ( sK2(k5_relat_1(sK0,sK1)) != sK2(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_7164 ),
    inference(superposition,[],[f63,f95363])).

fof(f95363,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ spl5_7164 ),
    inference(avatar_component_clause,[],[f95362])).

fof(f95362,plain,
    ( spl5_7164
  <=> sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7164])])).

fof(f63,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',d8_funct_1)).

fof(f95364,plain,
    ( spl5_7164
    | ~ spl5_128
    | ~ spl5_6988 ),
    inference(avatar_split_clause,[],[f95337,f94294,f729,f95362])).

fof(f729,plain,
    ( spl5_128
  <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f94294,plain,
    ( spl5_6988
  <=> ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6988])])).

fof(f95337,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ spl5_128
    | ~ spl5_6988 ),
    inference(subsumption_resolution,[],[f95336,f730])).

fof(f730,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f729])).

fof(f95336,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_6988 ),
    inference(equality_resolution,[],[f94295])).

fof(f94295,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    | ~ spl5_6988 ),
    inference(avatar_component_clause,[],[f94294])).

fof(f94298,plain,
    ( spl5_6988
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_136
    | ~ spl5_2136 ),
    inference(avatar_split_clause,[],[f24808,f24757,f767,f109,f88,f81,f94294])).

fof(f81,plain,
    ( spl5_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f88,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f109,plain,
    ( spl5_8
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f767,plain,
    ( spl5_136
  <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f24757,plain,
    ( spl5_2136
  <=> k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2136])])).

fof(f24808,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0)) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_136
    | ~ spl5_2136 ),
    inference(subsumption_resolution,[],[f24807,f82])).

fof(f82,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f24807,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_136
    | ~ spl5_2136 ),
    inference(subsumption_resolution,[],[f24806,f89])).

fof(f89,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f24806,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_8
    | ~ spl5_136
    | ~ spl5_2136 ),
    inference(subsumption_resolution,[],[f24805,f110])).

fof(f110,plain,
    ( v2_funct_1(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f24805,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_136
    | ~ spl5_2136 ),
    inference(subsumption_resolution,[],[f24794,f768])).

fof(f768,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_136 ),
    inference(avatar_component_clause,[],[f767])).

fof(f24794,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2136 ),
    inference(superposition,[],[f59,f24758])).

fof(f24758,plain,
    ( k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))
    | ~ spl5_2136 ),
    inference(avatar_component_clause,[],[f24757])).

fof(f59,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f24774,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_926
    | spl5_2139 ),
    inference(avatar_contradiction_clause,[],[f24773])).

fof(f24773,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_926
    | ~ spl5_2139 ),
    inference(subsumption_resolution,[],[f24772,f96])).

fof(f96,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f24772,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_926
    | ~ spl5_2139 ),
    inference(subsumption_resolution,[],[f24771,f103])).

fof(f103,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f24771,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_926
    | ~ spl5_2139 ),
    inference(subsumption_resolution,[],[f24770,f82])).

fof(f24770,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_926
    | ~ spl5_2139 ),
    inference(subsumption_resolution,[],[f24769,f89])).

fof(f24769,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_926
    | ~ spl5_2139 ),
    inference(subsumption_resolution,[],[f24767,f7074])).

fof(f7074,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl5_926 ),
    inference(avatar_component_clause,[],[f7073])).

fof(f7073,plain,
    ( spl5_926
  <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_926])])).

fof(f24767,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2139 ),
    inference(resolution,[],[f24764,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',t21_funct_1)).

fof(f24764,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl5_2139 ),
    inference(avatar_component_clause,[],[f24763])).

fof(f24763,plain,
    ( spl5_2139
  <=> ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2139])])).

fof(f24765,plain,
    ( spl5_2136
    | ~ spl5_2139
    | ~ spl5_858 ),
    inference(avatar_split_clause,[],[f6518,f6495,f24763,f24757])).

fof(f6495,plain,
    ( spl5_858
  <=> ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_858])])).

fof(f6518,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))
    | ~ spl5_858 ),
    inference(equality_resolution,[],[f6496])).

fof(f6496,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2 )
    | ~ spl5_858 ),
    inference(avatar_component_clause,[],[f6495])).

fof(f7088,plain,
    ( spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | spl5_927 ),
    inference(avatar_contradiction_clause,[],[f7087])).

fof(f7087,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_927 ),
    inference(subsumption_resolution,[],[f7086,f270])).

fof(f7086,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_42
    | ~ spl5_927 ),
    inference(subsumption_resolution,[],[f7085,f276])).

fof(f7085,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_927 ),
    inference(subsumption_resolution,[],[f7083,f131])).

fof(f7083,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_927 ),
    inference(resolution,[],[f7077,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7077,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl5_927 ),
    inference(avatar_component_clause,[],[f7076])).

fof(f7076,plain,
    ( spl5_927
  <=> ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_927])])).

fof(f6506,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_138
    | spl5_857 ),
    inference(avatar_contradiction_clause,[],[f6505])).

fof(f6505,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_138
    | ~ spl5_857 ),
    inference(subsumption_resolution,[],[f6504,f96])).

fof(f6504,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_138
    | ~ spl5_857 ),
    inference(subsumption_resolution,[],[f6503,f103])).

fof(f6503,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_138
    | ~ spl5_857 ),
    inference(subsumption_resolution,[],[f6502,f82])).

fof(f6502,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_138
    | ~ spl5_857 ),
    inference(subsumption_resolution,[],[f6501,f89])).

fof(f6501,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_138
    | ~ spl5_857 ),
    inference(subsumption_resolution,[],[f6499,f778])).

fof(f778,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl5_138 ),
    inference(avatar_component_clause,[],[f777])).

fof(f777,plain,
    ( spl5_138
  <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f6499,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_857 ),
    inference(resolution,[],[f6493,f72])).

fof(f6493,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl5_857 ),
    inference(avatar_component_clause,[],[f6492])).

fof(f6492,plain,
    ( spl5_857
  <=> ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_857])])).

fof(f6497,plain,
    ( ~ spl5_857
    | spl5_858
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_180 ),
    inference(avatar_split_clause,[],[f1004,f989,f116,f102,f95,f6495,f6492])).

fof(f116,plain,
    ( spl5_10
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f989,plain,
    ( spl5_180
  <=> k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f1004,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_180 ),
    inference(subsumption_resolution,[],[f1003,f96])).

fof(f1003,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_180 ),
    inference(subsumption_resolution,[],[f1002,f103])).

fof(f1002,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_10
    | ~ spl5_180 ),
    inference(subsumption_resolution,[],[f995,f117])).

fof(f117,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f995,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_180 ),
    inference(superposition,[],[f59,f990])).

fof(f990,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl5_180 ),
    inference(avatar_component_clause,[],[f989])).

fof(f992,plain,
    ( spl5_180
    | ~ spl5_78
    | ~ spl5_138
    | ~ spl5_154 ),
    inference(avatar_split_clause,[],[f973,f861,f777,f467,f989])).

fof(f467,plain,
    ( spl5_78
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f861,plain,
    ( spl5_154
  <=> k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f973,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl5_78
    | ~ spl5_138
    | ~ spl5_154 ),
    inference(forward_demodulation,[],[f800,f862])).

fof(f862,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl5_154 ),
    inference(avatar_component_clause,[],[f861])).

fof(f800,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl5_78
    | ~ spl5_138 ),
    inference(resolution,[],[f778,f468])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f467])).

fof(f863,plain,
    ( spl5_154
    | spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f845,f467,f284,f275,f269,f130,f861])).

fof(f284,plain,
    ( spl5_44
  <=> k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f845,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_78 ),
    inference(backward_demodulation,[],[f500,f285])).

fof(f285,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f284])).

fof(f500,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_78 ),
    inference(subsumption_resolution,[],[f499,f270])).

fof(f499,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_42
    | ~ spl5_78 ),
    inference(subsumption_resolution,[],[f498,f276])).

fof(f498,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_78 ),
    inference(subsumption_resolution,[],[f493,f131])).

fof(f493,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_78 ),
    inference(resolution,[],[f468,f60])).

fof(f799,plain,
    ( spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | spl5_139 ),
    inference(avatar_contradiction_clause,[],[f798])).

fof(f798,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_40
    | ~ spl5_42
    | ~ spl5_139 ),
    inference(subsumption_resolution,[],[f797,f270])).

fof(f797,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_42
    | ~ spl5_139 ),
    inference(subsumption_resolution,[],[f796,f276])).

fof(f796,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_139 ),
    inference(subsumption_resolution,[],[f794,f131])).

fof(f794,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_139 ),
    inference(resolution,[],[f781,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f781,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl5_139 ),
    inference(avatar_component_clause,[],[f780])).

fof(f780,plain,
    ( spl5_139
  <=> ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f769,plain,
    ( spl5_136
    | spl5_15
    | ~ spl5_28
    | ~ spl5_40
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f758,f275,f269,f208,f130,f767])).

fof(f208,plain,
    ( spl5_28
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | r2_hidden(X0,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f758,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_15
    | ~ spl5_28
    | ~ spl5_40
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f757,f270])).

fof(f757,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_28
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f238,f276])).

fof(f238,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f235,f131])).

fof(f235,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_28 ),
    inference(resolution,[],[f209,f61])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f731,plain,
    ( spl5_128
    | spl5_15
    | ~ spl5_28
    | ~ spl5_40
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f720,f275,f269,f208,f130,f729])).

fof(f720,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_15
    | ~ spl5_28
    | ~ spl5_40
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f719,f270])).

fof(f719,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_28
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f237,f276])).

fof(f237,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f234,f131])).

fof(f234,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_28 ),
    inference(resolution,[],[f209,f60])).

fof(f469,plain,
    ( spl5_78
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f242,f220,f88,f81,f467])).

fof(f220,plain,
    ( spl5_34
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(X3,sK1),X2) = k1_funct_1(sK1,k1_funct_1(X3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f239,f82])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | ~ v1_relat_1(sK0)
        | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl5_2
    | ~ spl5_34 ),
    inference(resolution,[],[f221,f89])).

fof(f221,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(X3,sK1),X2) = k1_funct_1(sK1,k1_funct_1(X3,X2)) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f220])).

fof(f300,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f298,f82])).

fof(f298,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f297,f89])).

fof(f297,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f296,f96])).

fof(f296,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f294,f103])).

fof(f294,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_43 ),
    inference(resolution,[],[f279,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',fc2_funct_1)).

fof(f279,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl5_43
  <=> ~ v1_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f292,plain,
    ( ~ spl5_0
    | ~ spl5_4
    | spl5_41 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f290,f82])).

fof(f290,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_4
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f288,f96])).

fof(f288,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl5_41 ),
    inference(resolution,[],[f273,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',dt_k5_relat_1)).

fof(f273,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl5_41
  <=> ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f286,plain,
    ( ~ spl5_41
    | ~ spl5_43
    | spl5_44
    | spl5_15 ),
    inference(avatar_split_clause,[],[f156,f130,f284,f278,f272])).

fof(f156,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl5_15 ),
    inference(resolution,[],[f62,f131])).

fof(f62,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f222,plain,
    ( spl5_34
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f187,f102,f95,f220])).

fof(f187,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(X3,sK1),X2) = k1_funct_1(sK1,k1_funct_1(X3,X2)) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f184,f96])).

fof(f184,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(k5_relat_1(X3,sK1),X2) = k1_funct_1(sK1,k1_funct_1(X3,X2))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f70,f103])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',t22_funct_1)).

fof(f210,plain,
    ( spl5_28
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f196,f172,f88,f81,f208])).

fof(f172,plain,
    ( spl5_22
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | r2_hidden(X2,k1_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f193,f82])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | ~ v1_relat_1(sK0)
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(resolution,[],[f173,f89])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_relat_1(X3)
        | r2_hidden(X2,k1_relat_1(X3)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f161,f102,f95,f172])).

fof(f161,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | r2_hidden(X2,k1_relat_1(X3)) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f158,f96])).

fof(f158,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X3,sK1)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | r2_hidden(X2,k1_relat_1(X3))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f71,f103])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f132,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f56,f130])).

fof(f56,plain,(
    ~ v2_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    & v2_funct_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(k5_relat_1(X0,X1))
            & v2_funct_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(sK0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_funct_1(k5_relat_1(X0,sK1))
        & v2_funct_1(sK1)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
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
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t46_funct_1.p',t46_funct_1)).

fof(f118,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
