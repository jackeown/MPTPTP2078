%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0655+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 246 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  583 (1075 expanded)
%              Number of equality atoms :  137 ( 222 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f96,f119,f127,f136,f182,f205,f210,f243,f292,f317])).

fof(f317,plain,
    ( spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f315,f109])).

fof(f109,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f315,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f314,f113])).

fof(f113,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_7
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f314,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f312,f82])).

fof(f82,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_4
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f312,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl5_19 ),
    inference(trivial_inequality_removal,[],[f310])).

fof(f310,plain,
    ( sK3(k2_funct_1(sK0)) != sK3(k2_funct_1(sK0))
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl5_19 ),
    inference(superposition,[],[f52,f291])).

fof(f291,plain,
    ( sK3(k2_funct_1(sK0)) = sK4(k2_funct_1(sK0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl5_19
  <=> sK3(k2_funct_1(sK0)) = sK4(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f52,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f292,plain,
    ( spl5_19
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f281,f240,f207,f202,f289])).

fof(f202,plain,
    ( spl5_12
  <=> sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f207,plain,
    ( spl5_13
  <=> k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f240,plain,
    ( spl5_16
  <=> sK3(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f281,plain,
    ( sK3(k2_funct_1(sK0)) = sK4(k2_funct_1(sK0))
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f256,f242])).

fof(f242,plain,
    ( sK3(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f240])).

fof(f256,plain,
    ( sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f204,f209])).

fof(f209,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f207])).

fof(f204,plain,
    ( sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f202])).

fof(f243,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f193,f179,f75,f70,f65,f240])).

fof(f65,plain,
    ( spl5_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f75,plain,
    ( spl5_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f179,plain,
    ( spl5_10
  <=> r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f193,plain,
    ( sK3(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f192,f67])).

fof(f67,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f192,plain,
    ( sK3(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f191,f72])).

fof(f72,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f191,plain,
    ( sK3(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f187,f77])).

fof(f77,plain,
    ( v2_funct_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f187,plain,
    ( sK3(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f181,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f181,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f210,plain,
    ( spl5_13
    | spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f200,f112,f108,f80,f207])).

fof(f200,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f199,f109])).

fof(f199,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f84,f113])).

fof(f84,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4 ),
    inference(resolution,[],[f51,f82])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f205,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f151,f116,f75,f70,f65,f202])).

fof(f116,plain,
    ( spl5_8
  <=> r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f151,plain,
    ( sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f150,f67])).

fof(f150,plain,
    ( sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f149,f72])).

fof(f149,plain,
    ( sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f145,f77])).

fof(f145,plain,
    ( sK4(k2_funct_1(sK0)) = k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f118,f53])).

fof(f118,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f182,plain,
    ( spl5_10
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f173,f112,f108,f93,f80,f179])).

fof(f93,plain,
    ( spl5_5
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f173,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f172,f109])).

fof(f172,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f102,f113])).

fof(f102,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f100,f82])).

fof(f100,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f49,f95])).

fof(f95,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_7 ),
    inference(subsumption_resolution,[],[f134,f67])).

fof(f134,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_2
    | spl5_7 ),
    inference(subsumption_resolution,[],[f132,f72])).

fof(f132,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_7 ),
    inference(resolution,[],[f114,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f114,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f127,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f125,f67])).

fof(f125,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f123,f72])).

fof(f123,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_6 ),
    inference(resolution,[],[f110,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f110,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f119,plain,
    ( ~ spl5_6
    | ~ spl5_7
    | spl5_8
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f101,f93,f80,f116,f112,f108])).

fof(f101,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f99,f82])).

fof(f99,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f50,f95])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f91,f75,f70,f65,f93])).

% (8106)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f91,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f90,f67])).

fof(f90,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f87,f72])).

fof(f87,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f86,f77])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f85,f32])).

fof(f85,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f63,f33])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK2(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
                  | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
                & sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
              | ( ( sK1(X0,X1) != k1_funct_1(X0,sK2(X0,X1))
                  | ~ r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                & sK2(X0,X1) = k1_funct_1(X1,sK1(X0,X1))
                & r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK2(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
            | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
          & sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
        | ( ( sK1(X0,X1) != k1_funct_1(X0,sK2(X0,X1))
            | ~ r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          & sK2(X0,X1) = k1_funct_1(X1,sK1(X0,X1))
          & r2_hidden(sK1(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f83,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f78,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

% (8108)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (8124)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f73,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
