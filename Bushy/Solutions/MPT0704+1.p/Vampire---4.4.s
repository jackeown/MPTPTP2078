%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t159_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 391 expanded)
%              Number of leaves         :   52 ( 163 expanded)
%              Depth                    :   12
%              Number of atoms          :  822 (1510 expanded)
%              Number of equality atoms :  173 ( 328 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f156,f163,f174,f178,f182,f216,f224,f248,f270,f281,f416,f440,f478,f487,f492,f686,f702,f748,f1660,f2450,f3967,f3978,f3982,f4003,f7259,f7626,f7630])).

fof(f7630,plain,(
    ~ spl12_766 ),
    inference(avatar_contradiction_clause,[],[f7627])).

fof(f7627,plain,
    ( $false
    | ~ spl12_766 ),
    inference(unit_resulting_resolution,[],[f139,f7625])).

fof(f7625,plain,
    ( ! [X1] : ~ r1_tarski(k1_tarski(sK3(sK0,sK1)),k1_tarski(X1))
    | ~ spl12_766 ),
    inference(avatar_component_clause,[],[f7624])).

fof(f7624,plain,
    ( spl12_766
  <=> ! [X1] : ~ r1_tarski(k1_tarski(sK3(sK0,sK1)),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_766])])).

fof(f139,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t39_zfmisc_1)).

fof(f7626,plain,
    ( spl12_766
    | ~ spl12_18
    | spl12_189
    | ~ spl12_734 ),
    inference(avatar_split_clause,[],[f7602,f7221,f1642,f214,f7624])).

fof(f214,plain,
    ( spl12_18
  <=> ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f1642,plain,
    ( spl12_189
  <=> k10_relat_1(sK0,k1_tarski(sK1)) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_189])])).

fof(f7221,plain,
    ( spl12_734
  <=> ! [X0] :
        ( k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0))
        | k10_relat_1(sK0,k1_tarski(X0)) = o_0_0_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_734])])).

fof(f7602,plain,
    ( ! [X1] : ~ r1_tarski(k1_tarski(sK3(sK0,sK1)),k1_tarski(X1))
    | ~ spl12_18
    | ~ spl12_189
    | ~ spl12_734 ),
    inference(subsumption_resolution,[],[f7570,f1643])).

fof(f1643,plain,
    ( k10_relat_1(sK0,k1_tarski(sK1)) != o_0_0_xboole_0
    | ~ spl12_189 ),
    inference(avatar_component_clause,[],[f1642])).

fof(f7570,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(sK3(sK0,sK1)),k1_tarski(X1))
        | k10_relat_1(sK0,k1_tarski(sK1)) = o_0_0_xboole_0 )
    | ~ spl12_18
    | ~ spl12_734 ),
    inference(superposition,[],[f215,f7222])).

fof(f7222,plain,
    ( ! [X0] :
        ( k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0))
        | k10_relat_1(sK0,k1_tarski(X0)) = o_0_0_xboole_0 )
    | ~ spl12_734 ),
    inference(avatar_component_clause,[],[f7221])).

fof(f215,plain,
    ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f7259,plain,
    ( spl12_734
    | ~ spl12_90
    | ~ spl12_94 ),
    inference(avatar_split_clause,[],[f5234,f746,f700,f7221])).

fof(f700,plain,
    ( spl12_90
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_90])])).

fof(f746,plain,
    ( spl12_94
  <=> ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = o_0_0_xboole_0
        | r2_hidden(X0,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_94])])).

fof(f5234,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = o_0_0_xboole_0
        | k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl12_90
    | ~ spl12_94 ),
    inference(resolution,[],[f747,f701])).

fof(f701,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl12_90 ),
    inference(avatar_component_clause,[],[f700])).

fof(f747,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = o_0_0_xboole_0 )
    | ~ spl12_94 ),
    inference(avatar_component_clause,[],[f746])).

fof(f4003,plain,(
    ~ spl12_440 ),
    inference(avatar_contradiction_clause,[],[f3993])).

fof(f3993,plain,
    ( $false
    | ~ spl12_440 ),
    inference(unit_resulting_resolution,[],[f137,f3981,f138])).

fof(f138,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f80,f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',d1_tarski)).

fof(f3981,plain,
    ( ! [X5] : k1_tarski(X5) != k1_tarski(sK2(sK4(sK0)))
    | ~ spl12_440 ),
    inference(avatar_component_clause,[],[f3980])).

fof(f3980,plain,
    ( spl12_440
  <=> ! [X5] : k1_tarski(X5) != k1_tarski(sK2(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_440])])).

fof(f137,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f3982,plain,
    ( spl12_312
    | spl12_440
    | ~ spl12_0
    | ~ spl12_2
    | spl12_17
    | ~ spl12_70 ),
    inference(avatar_split_clause,[],[f3289,f485,f211,f154,f147,f3980,f2487])).

fof(f2487,plain,
    ( spl12_312
  <=> k10_relat_1(sK0,k1_tarski(sK4(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_312])])).

fof(f147,plain,
    ( spl12_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f154,plain,
    ( spl12_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f211,plain,
    ( spl12_17
  <=> ~ v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f485,plain,
    ( spl12_70
  <=> ! [X1] :
        ( k1_tarski(sK2(X1)) = k10_relat_1(sK0,k1_tarski(X1))
        | k10_relat_1(sK0,k1_tarski(X1)) = o_0_0_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f3289,plain,
    ( ! [X5] :
        ( k1_tarski(X5) != k1_tarski(sK2(sK4(sK0)))
        | k10_relat_1(sK0,k1_tarski(sK4(sK0))) = o_0_0_xboole_0 )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_17
    | ~ spl12_70 ),
    inference(subsumption_resolution,[],[f3288,f148])).

fof(f148,plain,
    ( v1_relat_1(sK0)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f147])).

fof(f3288,plain,
    ( ! [X5] :
        ( k1_tarski(X5) != k1_tarski(sK2(sK4(sK0)))
        | ~ v1_relat_1(sK0)
        | k10_relat_1(sK0,k1_tarski(sK4(sK0))) = o_0_0_xboole_0 )
    | ~ spl12_2
    | ~ spl12_17
    | ~ spl12_70 ),
    inference(subsumption_resolution,[],[f3287,f155])).

fof(f155,plain,
    ( v1_funct_1(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f154])).

fof(f3287,plain,
    ( ! [X5] :
        ( k1_tarski(X5) != k1_tarski(sK2(sK4(sK0)))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k10_relat_1(sK0,k1_tarski(sK4(sK0))) = o_0_0_xboole_0 )
    | ~ spl12_17
    | ~ spl12_70 ),
    inference(subsumption_resolution,[],[f3284,f212])).

fof(f212,plain,
    ( ~ v2_funct_1(sK0)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f211])).

fof(f3284,plain,
    ( ! [X5] :
        ( k1_tarski(X5) != k1_tarski(sK2(sK4(sK0)))
        | v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k10_relat_1(sK0,k1_tarski(sK4(sK0))) = o_0_0_xboole_0 )
    | ~ spl12_70 ),
    inference(superposition,[],[f94,f486])).

fof(f486,plain,
    ( ! [X1] :
        ( k1_tarski(sK2(X1)) = k10_relat_1(sK0,k1_tarski(X1))
        | k10_relat_1(sK0,k1_tarski(X1)) = o_0_0_xboole_0 )
    | ~ spl12_70 ),
    inference(avatar_component_clause,[],[f485])).

fof(f94,plain,(
    ! [X4,X0] :
      ( k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0)))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( k1_tarski(sK3(X0,X1)) = k10_relat_1(X0,k1_tarski(X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0)))
            & r2_hidden(sK4(X0),k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
     => k1_tarski(sK3(X0,X1)) = k10_relat_1(X0,k1_tarski(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(X3))
          & r2_hidden(X3,k2_relat_1(X0)) )
     => ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0)))
        & r2_hidden(sK4(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X3] :
              ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(X3))
              & r2_hidden(X3,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X1] :
              ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
              & r2_hidden(X1,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t144_funct_1)).

fof(f3978,plain,
    ( ~ spl12_10
    | ~ spl12_312
    | ~ spl12_436 ),
    inference(avatar_contradiction_clause,[],[f3977])).

fof(f3977,plain,
    ( $false
    | ~ spl12_10
    | ~ spl12_312
    | ~ spl12_436 ),
    inference(subsumption_resolution,[],[f3976,f181])).

fof(f181,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl12_10
  <=> ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f3976,plain,
    ( r2_hidden(sK7(sK0,sK4(sK0)),o_0_0_xboole_0)
    | ~ spl12_312
    | ~ spl12_436 ),
    inference(forward_demodulation,[],[f3973,f2488])).

fof(f2488,plain,
    ( k10_relat_1(sK0,k1_tarski(sK4(sK0))) = o_0_0_xboole_0
    | ~ spl12_312 ),
    inference(avatar_component_clause,[],[f2487])).

fof(f3973,plain,
    ( r2_hidden(sK7(sK0,sK4(sK0)),k10_relat_1(sK0,k1_tarski(sK4(sK0))))
    | ~ spl12_436 ),
    inference(resolution,[],[f3966,f137])).

fof(f3966,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0),X0)
        | r2_hidden(sK7(sK0,sK4(sK0)),k10_relat_1(sK0,X0)) )
    | ~ spl12_436 ),
    inference(avatar_component_clause,[],[f3965])).

fof(f3965,plain,
    ( spl12_436
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK0),X0)
        | r2_hidden(sK7(sK0,sK4(sK0)),k10_relat_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_436])])).

fof(f3967,plain,
    ( spl12_436
    | ~ spl12_26
    | ~ spl12_88
    | ~ spl12_290 ),
    inference(avatar_split_clause,[],[f3680,f2382,f684,f246,f3965])).

fof(f246,plain,
    ( spl12_26
  <=> r2_hidden(sK4(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f684,plain,
    ( spl12_88
  <=> k1_funct_1(sK0,sK7(sK0,sK4(sK0))) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_88])])).

fof(f2382,plain,
    ( spl12_290
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK7(sK0,X0)),X1)
        | r2_hidden(sK7(sK0,X0),k10_relat_1(sK0,X1))
        | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_290])])).

fof(f3680,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0),X0)
        | r2_hidden(sK7(sK0,sK4(sK0)),k10_relat_1(sK0,X0)) )
    | ~ spl12_26
    | ~ spl12_88
    | ~ spl12_290 ),
    inference(subsumption_resolution,[],[f3675,f247])).

fof(f247,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f3675,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0),X0)
        | r2_hidden(sK7(sK0,sK4(sK0)),k10_relat_1(sK0,X0))
        | ~ r2_hidden(sK4(sK0),k2_relat_1(sK0)) )
    | ~ spl12_88
    | ~ spl12_290 ),
    inference(superposition,[],[f2383,f685])).

fof(f685,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK4(sK0))) = sK4(sK0)
    | ~ spl12_88 ),
    inference(avatar_component_clause,[],[f684])).

fof(f2383,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK7(sK0,X0)),X1)
        | r2_hidden(sK7(sK0,X0),k10_relat_1(sK0,X1))
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl12_290 ),
    inference(avatar_component_clause,[],[f2382])).

fof(f2450,plain,
    ( spl12_290
    | ~ spl12_64
    | ~ spl12_72 ),
    inference(avatar_split_clause,[],[f1322,f490,f438,f2382])).

fof(f438,plain,
    ( spl12_64
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f490,plain,
    ( spl12_72
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k1_funct_1(sK0,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(X0,k10_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).

fof(f1322,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK7(sK0,X2)),X3)
        | r2_hidden(sK7(sK0,X2),k10_relat_1(sK0,X3))
        | ~ r2_hidden(X2,k2_relat_1(sK0)) )
    | ~ spl12_64
    | ~ spl12_72 ),
    inference(resolution,[],[f491,f439])).

fof(f439,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl12_64 ),
    inference(avatar_component_clause,[],[f438])).

fof(f491,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(k1_funct_1(sK0,X0),X1)
        | r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl12_72 ),
    inference(avatar_component_clause,[],[f490])).

fof(f1660,plain,
    ( ~ spl12_8
    | ~ spl12_18
    | ~ spl12_188 ),
    inference(avatar_contradiction_clause,[],[f1659])).

fof(f1659,plain,
    ( $false
    | ~ spl12_8
    | ~ spl12_18
    | ~ spl12_188 ),
    inference(subsumption_resolution,[],[f1651,f177])).

fof(f177,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl12_8
  <=> ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f1651,plain,
    ( ! [X2] : ~ r1_tarski(o_0_0_xboole_0,k1_tarski(X2))
    | ~ spl12_18
    | ~ spl12_188 ),
    inference(backward_demodulation,[],[f1646,f215])).

fof(f1646,plain,
    ( k10_relat_1(sK0,k1_tarski(sK1)) = o_0_0_xboole_0
    | ~ spl12_188 ),
    inference(avatar_component_clause,[],[f1645])).

fof(f1645,plain,
    ( spl12_188
  <=> k10_relat_1(sK0,k1_tarski(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_188])])).

fof(f748,plain,
    ( spl12_94
    | ~ spl12_58 ),
    inference(avatar_split_clause,[],[f426,f414,f746])).

fof(f414,plain,
    ( spl12_58
  <=> ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
        | k10_relat_1(sK0,X0) = o_0_0_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f426,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = o_0_0_xboole_0
        | r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl12_58 ),
    inference(resolution,[],[f415,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f111,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',symmetry_r1_xboole_0)).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t56_zfmisc_1)).

fof(f415,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
        | k10_relat_1(sK0,X0) = o_0_0_xboole_0 )
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f414])).

fof(f702,plain,
    ( spl12_90
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_16 ),
    inference(avatar_split_clause,[],[f692,f208,f154,f147,f700])).

fof(f208,plain,
    ( spl12_16
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f692,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f691,f148])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl12_2
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f690,f155])).

fof(f690,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_tarski(sK3(sK0,X0)) = k10_relat_1(sK0,k1_tarski(X0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl12_16 ),
    inference(resolution,[],[f209,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | k1_tarski(sK3(X0,X1)) = k10_relat_1(X0,k1_tarski(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f209,plain,
    ( v2_funct_1(sK0)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f686,plain,
    ( spl12_88
    | ~ spl12_26
    | ~ spl12_68 ),
    inference(avatar_split_clause,[],[f480,f476,f246,f684])).

fof(f476,plain,
    ( spl12_68
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,sK7(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f480,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK4(sK0))) = sK4(sK0)
    | ~ spl12_26
    | ~ spl12_68 ),
    inference(resolution,[],[f477,f247])).

fof(f477,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,sK7(sK0,X0)) = X0 )
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f476])).

fof(f492,plain,
    ( spl12_72
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f350,f154,f147,f490])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK0,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(X0,k10_relat_1(sK0,X1)) )
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f349,f148])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK0,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(X0,k10_relat_1(sK0,X1))
        | ~ v1_relat_1(sK0) )
    | ~ spl12_2 ),
    inference(resolution,[],[f133,f155])).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
                | ~ r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK8(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
                  & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',d13_funct_1)).

fof(f487,plain,
    ( spl12_70
    | ~ spl12_20
    | ~ spl12_36 ),
    inference(avatar_split_clause,[],[f290,f279,f222,f485])).

fof(f222,plain,
    ( spl12_20
  <=> ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f279,plain,
    ( spl12_36
  <=> ! [X1,X0] :
        ( o_0_0_xboole_0 = X0
        | k1_tarski(X1) = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f290,plain,
    ( ! [X1] :
        ( k1_tarski(sK2(X1)) = k10_relat_1(sK0,k1_tarski(X1))
        | k10_relat_1(sK0,k1_tarski(X1)) = o_0_0_xboole_0 )
    | ~ spl12_20
    | ~ spl12_36 ),
    inference(resolution,[],[f280,f223])).

fof(f223,plain,
    ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f222])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tarski(X1))
        | k1_tarski(X1) = X0
        | o_0_0_xboole_0 = X0 )
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f279])).

fof(f478,plain,
    ( spl12_68
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f345,f154,f147,f476])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,sK7(sK0,X0)) = X0 )
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f344,f148])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k1_funct_1(sK0,sK7(sK0,X0)) = X0
        | ~ v1_relat_1(sK0) )
    | ~ spl12_2 ),
    inference(resolution,[],[f131,f155])).

fof(f131,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f66,f69,f68,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',d5_funct_1)).

fof(f440,plain,
    ( spl12_64
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f336,f154,f147,f438])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(sK7(sK0,X0),k1_relat_1(sK0)) )
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f335,f148])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | r2_hidden(sK7(sK0,X0),k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl12_2 ),
    inference(resolution,[],[f132,f155])).

fof(f132,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f416,plain,
    ( spl12_58
    | ~ spl12_0
    | ~ spl12_32 ),
    inference(avatar_split_clause,[],[f287,f268,f147,f414])).

fof(f268,plain,
    ( spl12_32
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = o_0_0_xboole_0
        | ~ r1_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
        | k10_relat_1(sK0,X0) = o_0_0_xboole_0 )
    | ~ spl12_0
    | ~ spl12_32 ),
    inference(resolution,[],[f269,f148])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k10_relat_1(X1,X0) = o_0_0_xboole_0 )
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f281,plain,
    ( spl12_36
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f260,f172,f279])).

fof(f172,plain,
    ( spl12_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( o_0_0_xboole_0 = X0
        | k1_tarski(X1) = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) )
    | ~ spl12_6 ),
    inference(forward_demodulation,[],[f120,f173])).

fof(f173,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f172])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f270,plain,
    ( spl12_32
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f252,f172,f268])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = o_0_0_xboole_0
        | ~ r1_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl12_6 ),
    inference(forward_demodulation,[],[f110,f173])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t173_relat_1)).

fof(f248,plain,
    ( spl12_26
    | ~ spl12_0
    | ~ spl12_2
    | spl12_17 ),
    inference(avatar_split_clause,[],[f241,f211,f154,f147,f246])).

fof(f241,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f240,f148])).

fof(f240,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl12_2
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f239,f212])).

fof(f239,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_2 ),
    inference(resolution,[],[f93,f155])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0),k2_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f224,plain,
    ( spl12_20
    | spl12_17 ),
    inference(avatar_split_clause,[],[f217,f211,f222])).

fof(f217,plain,
    ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f88,f212])).

fof(f88,plain,(
    ! [X3] :
      ( r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
      | v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) )
    & ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
      | v2_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f55,f58,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ( ? [X1] :
            ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
          | ~ v2_funct_1(X0) )
        & ( ! [X3] :
            ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
          | v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(sK0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
     => ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(sK1)),k1_tarski(X2)) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
     => r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(sK2(X3))) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
        <=> ! [X1] :
            ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t159_funct_1)).

fof(f216,plain,
    ( ~ spl12_17
    | spl12_18 ),
    inference(avatar_split_clause,[],[f89,f214,f211])).

fof(f89,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f182,plain,
    ( spl12_10
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f165,f161,f180])).

fof(f161,plain,
    ( spl12_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f165,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl12_4 ),
    inference(resolution,[],[f126,f162])).

fof(f162,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t7_boole)).

fof(f178,plain,
    ( spl12_8
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f167,f161,f176])).

fof(f167,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl12_4 ),
    inference(backward_demodulation,[],[f164,f91])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t2_xboole_1)).

fof(f164,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl12_4 ),
    inference(resolution,[],[f92,f162])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',t6_boole)).

fof(f174,plain,
    ( spl12_6
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f164,f161,f172])).

fof(f163,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f90,f161])).

fof(f90,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t159_funct_1.p',dt_o_0_0_xboole_0)).

fof(f156,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f87,f154])).

fof(f87,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f149,plain,(
    spl12_0 ),
    inference(avatar_split_clause,[],[f86,f147])).

fof(f86,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
