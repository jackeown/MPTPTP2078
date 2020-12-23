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
% DateTime   : Thu Dec  3 12:52:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 301 expanded)
%              Number of leaves         :   20 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :  655 (1579 expanded)
%              Number of equality atoms :  129 ( 430 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f79,f84,f132,f139,f147,f157,f169,f176,f196,f212,f222,f223,f227,f228])).

fof(f228,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f227,plain,
    ( spl5_17
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f226,f125,f81,f71,f66,f61,f56,f51,f46,f193])).

fof(f193,plain,
    ( spl5_17
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f46,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f51,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f56,plain,
    ( spl5_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f61,plain,
    ( spl5_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f66,plain,
    ( spl5_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f71,plain,
    ( spl5_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f81,plain,
    ( spl5_8
  <=> k1_relat_1(sK1) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f125,plain,
    ( spl5_11
  <=> sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f226,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f123,f126])).

fof(f126,plain,
    ( sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f123,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f122,f73])).

fof(f73,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f122,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f121,f53])).

fof(f53,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f121,plain,
    ( ~ v1_funct_1(sK1)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f48,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f120,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,
    ( ! [X4] :
        ( k1_relat_1(sK1) != k1_relat_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4))
        | ~ sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0)
        | k2_funct_1(sK0) = X4 )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f105,f63])).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f105,plain,
    ( ! [X4] :
        ( k1_relat_1(sK1) != k1_relat_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK0)
        | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4))
        | ~ sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0)
        | k2_funct_1(sK0) = X4 )
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f104,f58])).

fof(f58,plain,
    ( v2_funct_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f104,plain,
    ( ! [X4] :
        ( k1_relat_1(sK1) != k1_relat_1(X4)
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK0)
        | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4))
        | ~ sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0)
        | k2_funct_1(sK0) = X4 )
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f98,f68])).

fof(f68,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f98,plain,
    ( ! [X4] :
        ( k1_relat_1(sK1) != k1_relat_1(X4)
        | ~ v1_funct_1(sK0)
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK0)
        | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4))
        | ~ sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0)
        | k2_funct_1(sK0) = X4 )
    | ~ spl5_8 ),
    inference(superposition,[],[f30,f83])).

fof(f83,plain,
    ( k1_relat_1(sK1) = k2_relat_1(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
      | ~ sP4(sK3(X0,X1),sK2(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f223,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK2(sK0,sK1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1)))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f222,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f220,f126])).

fof(f220,plain,
    ( ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f219,f73])).

fof(f219,plain,
    ( ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f218,f146])).

fof(f146,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_14
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f218,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f217,f63])).

fof(f217,plain,
    ( ~ v1_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f216,f83])).

fof(f216,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f215,f53])).

fof(f215,plain,
    ( ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f214,f48])).

fof(f214,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f213,f58])).

fof(f213,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f140,f68])).

fof(f140,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f138,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
      | ~ sP4(sK3(X0,X1),sK2(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f138,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_13
  <=> r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f212,plain,
    ( ~ spl5_8
    | spl5_11
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl5_8
    | spl5_11
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f210,f131])).

fof(f131,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_12
  <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f210,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_8
    | spl5_11
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f209,f83])).

fof(f209,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | spl5_11
    | ~ spl5_17 ),
    inference(resolution,[],[f202,f127])).

fof(f127,plain,
    ( ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f202,plain,
    ( ! [X2] :
        ( sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,X2)
        | ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(X2)) )
    | ~ spl5_17 ),
    inference(superposition,[],[f42,f195])).

fof(f195,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP4(k1_funct_1(X1,X2),X2,X1,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | k1_funct_1(X1,X2) != X3
      | sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f196,plain,
    ( spl5_17
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f191,f144,f136,f129,f193])).

fof(f191,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f161,f131])).

fof(f161,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f148,f138])).

fof(f148,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl5_14 ),
    inference(superposition,[],[f34,f146])).

fof(f34,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK0))
      | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) = X2
      | k1_funct_1(sK0,X2) != X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k1_relat_1(X1) = k2_relat_1(X0)
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k1_relat_1(X1) = k2_relat_1(X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(f176,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f162,f129,f76,f51,f46,f173])).

fof(f173,plain,
    ( spl5_16
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f76,plain,
    ( spl5_7
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f162,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(resolution,[],[f131,f107])).

fof(f107,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f35,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f89,f48])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f85,f53])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_7 ),
    inference(superposition,[],[f33,f78])).

fof(f78,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f35,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) != X2
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f169,plain,
    ( spl5_15
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f163,f129,f76,f51,f46,f166])).

fof(f166,plain,
    ( spl5_15
  <=> r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f163,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(resolution,[],[f131,f90])).

fof(f157,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f155,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f155,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f154,f83])).

fof(f154,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f153,f63])).

fof(f153,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f152,f138])).

fof(f152,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f149,f68])).

fof(f149,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_14 ),
    inference(superposition,[],[f33,f146])).

fof(f147,plain,
    ( spl5_14
    | spl5_11 ),
    inference(avatar_split_clause,[],[f134,f125,f144])).

fof(f134,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | spl5_11 ),
    inference(resolution,[],[f127,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X2,X1,X0)
      | k1_funct_1(X0,X3) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f139,plain,
    ( spl5_13
    | spl5_11 ),
    inference(avatar_split_clause,[],[f133,f125,f136])).

fof(f133,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | spl5_11 ),
    inference(resolution,[],[f127,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X2,X1,X0)
      | r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f132,plain,
    ( ~ spl5_11
    | spl5_12
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f111,f81,f71,f66,f61,f56,f51,f46,f129,f125])).

fof(f111,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f110,f73])).

fof(f110,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f109,f53])).

fof(f109,plain,
    ( ~ v1_funct_1(sK1)
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f108,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,
    ( ! [X3] :
        ( k1_relat_1(sK1) != k1_relat_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | r2_hidden(sK2(sK0,X3),k1_relat_1(sK1))
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f102,f63])).

fof(f102,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK0,X3),k1_relat_1(sK1))
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k1_relat_1(sK1) != k1_relat_1(X3)
        | ~ v1_relat_1(sK0)
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f101,f58])).

fof(f101,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK0,X3),k1_relat_1(sK1))
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k1_relat_1(sK1) != k1_relat_1(X3)
        | ~ v1_relat_1(sK0)
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f97,f68])).

fof(f97,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK0,X3),k1_relat_1(sK1))
        | ~ v1_funct_1(sK0)
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k1_relat_1(sK1) != k1_relat_1(X3)
        | ~ v1_relat_1(sK0)
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl5_8 ),
    inference(superposition,[],[f29,f83])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP4(sK3(X0,X1),sK2(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f17,f81])).

fof(f17,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f16,f76])).

fof(f16,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f18,f71])).

fof(f18,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f20,f66])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f19,f61])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f15,f56])).

fof(f15,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f14,f51])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f13,f46])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (32605)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.43  % (32602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.46  % (32612)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.47  % (32603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (32600)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (32600)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f229,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f79,f84,f132,f139,f147,f157,f169,f176,f196,f212,f222,f223,f227,f228])).
% 0.19/0.47  fof(f228,plain,(
% 0.19/0.47    sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k1_relat_1(sK0))),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f227,plain,(
% 0.19/0.47    spl5_17 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f226,f125,f81,f71,f66,f61,f56,f51,f46,f193])).
% 0.19/0.47  fof(f193,plain,(
% 0.19/0.47    spl5_17 <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    spl5_1 <=> v1_relat_1(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    spl5_2 <=> v1_funct_1(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    spl5_3 <=> v2_funct_1(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    spl5_4 <=> v1_relat_1(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    spl5_5 <=> v1_funct_1(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    spl5_6 <=> sK1 = k2_funct_1(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    spl5_8 <=> k1_relat_1(sK1) = k2_relat_1(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.47  fof(f125,plain,(
% 0.19/0.47    spl5_11 <=> sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.47  fof(f226,plain,(
% 0.19/0.47    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_11)),
% 0.19/0.47    inference(subsumption_resolution,[],[f123,f126])).
% 0.19/0.47  fof(f126,plain,(
% 0.19/0.47    sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | ~spl5_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f125])).
% 0.19/0.47  fof(f123,plain,(
% 0.19/0.47    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f122,f73])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    sK1 != k2_funct_1(sK0) | spl5_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f71])).
% 0.19/0.47  fof(f122,plain,(
% 0.19/0.47    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f121,f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    v1_funct_1(sK1) | ~spl5_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f51])).
% 0.19/0.47  fof(f121,plain,(
% 0.19/0.47    ~v1_funct_1(sK1) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f120,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    v1_relat_1(sK1) | ~spl5_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f46])).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(equality_resolution,[],[f106])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    ( ! [X4] : (k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4)) | ~sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0) | k2_funct_1(sK0) = X4) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f105,f63])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    v1_relat_1(sK0) | ~spl5_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f61])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    ( ! [X4] : (k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(sK0) | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4)) | ~sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0) | k2_funct_1(sK0) = X4) ) | (~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f104,f58])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    v2_funct_1(sK0) | ~spl5_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f56])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    ( ! [X4] : (k1_relat_1(sK1) != k1_relat_1(X4) | ~v2_funct_1(sK0) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(sK0) | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4)) | ~sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0) | k2_funct_1(sK0) = X4) ) | (~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f98,f68])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    v1_funct_1(sK0) | ~spl5_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f66])).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    ( ! [X4] : (k1_relat_1(sK1) != k1_relat_1(X4) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(sK0) | sK3(sK0,X4) = k1_funct_1(X4,sK2(sK0,X4)) | ~sP4(sK3(sK0,X4),sK2(sK0,X4),X4,sK0) | k2_funct_1(sK0) = X4) ) | ~spl5_8),
% 0.19/0.47    inference(superposition,[],[f30,f83])).
% 0.19/0.47  fof(f83,plain,(
% 0.19/0.47    k1_relat_1(sK1) = k2_relat_1(sK0) | ~spl5_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f81])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1)) | ~sP4(sK3(X0,X1),sK2(X0,X1),X1,X0) | k2_funct_1(X0) = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f7])).
% 0.19/0.47  fof(f7,plain,(
% 0.19/0.47    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.19/0.47  fof(f223,plain,(
% 0.19/0.47    sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK2(sK0,sK1) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))),
% 0.19/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.47  fof(f222,plain,(
% 0.19/0.47    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_11 | ~spl5_13 | ~spl5_14),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f221])).
% 0.19/0.47  fof(f221,plain,(
% 0.19/0.47    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_11 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f220,f126])).
% 0.19/0.47  fof(f220,plain,(
% 0.19/0.47    ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f219,f73])).
% 0.19/0.47  fof(f219,plain,(
% 0.19/0.47    ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f218,f146])).
% 0.19/0.47  fof(f146,plain,(
% 0.19/0.47    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | ~spl5_14),
% 0.19/0.47    inference(avatar_component_clause,[],[f144])).
% 0.19/0.47  fof(f144,plain,(
% 0.19/0.47    spl5_14 <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.19/0.47  fof(f218,plain,(
% 0.19/0.47    sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f217,f63])).
% 0.19/0.47  fof(f217,plain,(
% 0.19/0.47    ~v1_relat_1(sK0) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_8 | ~spl5_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f216,f83])).
% 0.19/0.47  fof(f216,plain,(
% 0.19/0.47    k1_relat_1(sK1) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f215,f53])).
% 0.19/0.47  fof(f215,plain,(
% 0.19/0.47    ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_3 | ~spl5_5 | ~spl5_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f214,f48])).
% 0.19/0.47  fof(f214,plain,(
% 0.19/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_3 | ~spl5_5 | ~spl5_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f213,f58])).
% 0.19/0.47  fof(f213,plain,(
% 0.19/0.47    ~v2_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_5 | ~spl5_13)),
% 0.19/0.47    inference(subsumption_resolution,[],[f140,f68])).
% 0.19/0.47  fof(f140,plain,(
% 0.19/0.47    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK1) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | ~spl5_13),
% 0.19/0.47    inference(resolution,[],[f138,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_relat_1(X0) | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1)) | ~sP4(sK3(X0,X1),sK2(X0,X1),X1,X0) | k2_funct_1(X0) = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f138,plain,(
% 0.19/0.47    r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~spl5_13),
% 0.19/0.47    inference(avatar_component_clause,[],[f136])).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    spl5_13 <=> r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.19/0.47  fof(f212,plain,(
% 0.19/0.47    ~spl5_8 | spl5_11 | ~spl5_12 | ~spl5_17),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f211])).
% 0.19/0.47  fof(f211,plain,(
% 0.19/0.47    $false | (~spl5_8 | spl5_11 | ~spl5_12 | ~spl5_17)),
% 0.19/0.47    inference(subsumption_resolution,[],[f210,f131])).
% 0.19/0.47  fof(f131,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~spl5_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f129])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    spl5_12 <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.47  fof(f210,plain,(
% 0.19/0.47    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | (~spl5_8 | spl5_11 | ~spl5_17)),
% 0.19/0.47    inference(forward_demodulation,[],[f209,f83])).
% 0.19/0.47  fof(f209,plain,(
% 0.19/0.47    ~r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | (spl5_11 | ~spl5_17)),
% 0.19/0.47    inference(resolution,[],[f202,f127])).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | spl5_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f125])).
% 0.19/0.47  fof(f202,plain,(
% 0.19/0.47    ( ! [X2] : (sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,X2) | ~r2_hidden(sK2(sK0,sK1),k2_relat_1(X2))) ) | ~spl5_17),
% 0.19/0.47    inference(superposition,[],[f42,f195])).
% 0.19/0.47  fof(f195,plain,(
% 0.19/0.47    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~spl5_17),
% 0.19/0.47    inference(avatar_component_clause,[],[f193])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (sP4(k1_funct_1(X1,X2),X2,X1,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.19/0.47    inference(equality_resolution,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k2_relat_1(X0)) | k1_funct_1(X1,X2) != X3 | sP4(X3,X2,X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f196,plain,(
% 0.19/0.47    spl5_17 | ~spl5_12 | ~spl5_13 | ~spl5_14),
% 0.19/0.47    inference(avatar_split_clause,[],[f191,f144,f136,f129,f193])).
% 0.19/0.47  fof(f191,plain,(
% 0.19/0.47    sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f161,f131])).
% 0.19/0.47  fof(f161,plain,(
% 0.19/0.47    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | (~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f148,f138])).
% 0.19/0.47  fof(f148,plain,(
% 0.19/0.47    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~spl5_14),
% 0.19/0.47    inference(superposition,[],[f34,f146])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X2] : (~r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0)) | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2) )),
% 0.19/0.47    inference(equality_resolution,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3) )),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f5])).
% 0.19/0.47  fof(f5,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,negated_conjecture,(
% 0.19/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.19/0.47    inference(negated_conjecture,[],[f3])).
% 0.19/0.47  fof(f3,conjecture,(
% 0.19/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).
% 0.19/0.47  fof(f176,plain,(
% 0.19/0.47    spl5_16 | ~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f162,f129,f76,f51,f46,f173])).
% 0.19/0.47  fof(f173,plain,(
% 0.19/0.47    spl5_16 <=> sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    spl5_7 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.47  fof(f162,plain,(
% 0.19/0.47    sK2(sK0,sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK0,sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_12)),
% 0.19/0.47    inference(resolution,[],[f131,f107])).
% 0.19/0.47  fof(f107,plain,(
% 0.19/0.47    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) ) | (~spl5_1 | ~spl5_2 | ~spl5_7)),
% 0.19/0.47    inference(subsumption_resolution,[],[f35,f90])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_7)),
% 0.19/0.47    inference(subsumption_resolution,[],[f89,f48])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl5_2 | ~spl5_7)),
% 0.19/0.47    inference(subsumption_resolution,[],[f85,f53])).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl5_7),
% 0.19/0.47    inference(superposition,[],[f33,f78])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl5_7),
% 0.19/0.47    inference(avatar_component_clause,[],[f76])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.19/0.47    inference(equality_resolution,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) != X2 | k1_funct_1(sK0,X2) = X3) )),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f169,plain,(
% 0.19/0.47    spl5_15 | ~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f163,f129,f76,f51,f46,f166])).
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    spl5_15 <=> r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k1_relat_1(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.19/0.47  fof(f163,plain,(
% 0.19/0.47    r2_hidden(k1_funct_1(sK1,sK2(sK0,sK1)),k1_relat_1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_12)),
% 0.19/0.47    inference(resolution,[],[f131,f90])).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    ~spl5_4 | ~spl5_5 | ~spl5_8 | spl5_12 | ~spl5_13 | ~spl5_14),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f156])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    $false | (~spl5_4 | ~spl5_5 | ~spl5_8 | spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f155,f130])).
% 0.19/0.47  fof(f130,plain,(
% 0.19/0.47    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | spl5_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f129])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | (~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(forward_demodulation,[],[f154,f83])).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | (~spl5_4 | ~spl5_5 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f153,f63])).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl5_5 | ~spl5_13 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f152,f138])).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl5_5 | ~spl5_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f149,f68])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~spl5_14),
% 0.19/0.47    inference(superposition,[],[f33,f146])).
% 0.19/0.47  fof(f147,plain,(
% 0.19/0.47    spl5_14 | spl5_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f134,f125,f144])).
% 0.19/0.47  fof(f134,plain,(
% 0.19/0.47    sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) | spl5_11),
% 0.19/0.47    inference(resolution,[],[f127,f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (sP4(X3,X2,X1,X0) | k1_funct_1(X0,X3) = X2) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f139,plain,(
% 0.19/0.47    spl5_13 | spl5_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f133,f125,f136])).
% 0.19/0.47  fof(f133,plain,(
% 0.19/0.47    r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0)) | spl5_11),
% 0.19/0.47    inference(resolution,[],[f127,f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (sP4(X3,X2,X1,X0) | r2_hidden(X3,k1_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f132,plain,(
% 0.19/0.47    ~spl5_11 | spl5_12 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f111,f81,f71,f66,f61,f56,f51,f46,f129,f125])).
% 0.19/0.47  fof(f111,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f110,f73])).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f109,f53])).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    ~v1_funct_1(sK1) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f108,f48])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) | sK1 = k2_funct_1(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(equality_resolution,[],[f103])).
% 0.19/0.47  fof(f103,plain,(
% 0.19/0.47    ( ! [X3] : (k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | r2_hidden(sK2(sK0,X3),k1_relat_1(sK1)) | ~sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0) | k2_funct_1(sK0) = X3) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f102,f63])).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    ( ! [X3] : (r2_hidden(sK2(sK0,X3),k1_relat_1(sK1)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_relat_1(sK0) | ~sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0) | k2_funct_1(sK0) = X3) ) | (~spl5_3 | ~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f101,f58])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    ( ! [X3] : (r2_hidden(sK2(sK0,X3),k1_relat_1(sK1)) | ~v2_funct_1(sK0) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_relat_1(sK0) | ~sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0) | k2_funct_1(sK0) = X3) ) | (~spl5_5 | ~spl5_8)),
% 0.19/0.47    inference(subsumption_resolution,[],[f97,f68])).
% 0.19/0.47  fof(f97,plain,(
% 0.19/0.47    ( ! [X3] : (r2_hidden(sK2(sK0,X3),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_relat_1(sK1) != k1_relat_1(X3) | ~v1_relat_1(sK0) | ~sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0) | k2_funct_1(sK0) = X3) ) | ~spl5_8),
% 0.19/0.47    inference(superposition,[],[f29,f83])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_relat_1(X0) | ~sP4(sK3(X0,X1),sK2(X0,X1),X1,X0) | k2_funct_1(X0) = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    spl5_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f17,f81])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f79,plain,(
% 0.19/0.47    spl5_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f16,f76])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    ~spl5_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f18,f71])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    sK1 != k2_funct_1(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    spl5_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f20,f66])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    v1_funct_1(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    spl5_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f19,f61])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    v1_relat_1(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    spl5_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f15,f56])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    v2_funct_1(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    spl5_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f14,f51])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    v1_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    spl5_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f13,f46])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    v1_relat_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (32600)------------------------------
% 0.19/0.47  % (32600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (32600)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (32600)Memory used [KB]: 10746
% 0.19/0.47  % (32600)Time elapsed: 0.083 s
% 0.19/0.47  % (32600)------------------------------
% 0.19/0.47  % (32600)------------------------------
% 0.19/0.48  % (32596)Success in time 0.126 s
%------------------------------------------------------------------------------
