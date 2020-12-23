%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t62_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:26 EDT 2019

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 252 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  599 (1095 expanded)
%              Number of equality atoms :  137 ( 222 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f760,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f111,f118,f132,f172,f216,f225,f345,f398,f453,f657,f672,f749,f759])).

fof(f759,plain,
    ( spl6_9
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_102 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f757,f192])).

fof(f192,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_16
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f757,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f756,f198])).

fof(f198,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_18
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f756,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f754,f131])).

fof(f131,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_9
  <=> ~ v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f754,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_102 ),
    inference(trivial_inequality_removal,[],[f752])).

fof(f752,plain,
    ( sK3(k2_funct_1(sK0)) != sK3(k2_funct_1(sK0))
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_102 ),
    inference(superposition,[],[f79,f748])).

fof(f748,plain,
    ( sK3(k2_funct_1(sK0)) = sK4(k2_funct_1(sK0))
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f747])).

fof(f747,plain,
    ( spl6_102
  <=> sK3(k2_funct_1(sK0)) = sK4(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f79,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f49])).

fof(f49,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',d8_funct_1)).

fof(f749,plain,
    ( spl6_102
    | ~ spl6_88
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f729,f670,f655,f747])).

fof(f655,plain,
    ( spl6_88
  <=> k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f670,plain,
    ( spl6_92
  <=> k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK3(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f729,plain,
    ( sK3(k2_funct_1(sK0)) = sK4(k2_funct_1(sK0))
    | ~ spl6_88
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f671,f656])).

fof(f656,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f655])).

fof(f671,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK3(k2_funct_1(sK0))
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f670])).

fof(f672,plain,
    ( spl6_92
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f467,f451,f116,f109,f102,f670])).

fof(f102,plain,
    ( spl6_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f109,plain,
    ( spl6_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f116,plain,
    ( spl6_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f451,plain,
    ( spl6_54
  <=> r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f467,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK3(k2_funct_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f466,f103])).

fof(f103,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f102])).

fof(f466,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK3(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f465,f110])).

fof(f110,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f465,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK3(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f456,f117])).

fof(f117,plain,
    ( v2_funct_1(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f456,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK3(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_54 ),
    inference(resolution,[],[f452,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',t57_funct_1)).

fof(f452,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f451])).

fof(f657,plain,
    ( spl6_88
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_42
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f415,f396,f343,f116,f109,f102,f655])).

fof(f343,plain,
    ( spl6_42
  <=> k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f396,plain,
    ( spl6_50
  <=> r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f415,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_42
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f414,f344])).

fof(f344,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f343])).

fof(f414,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f413,f103])).

fof(f413,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f412,f110])).

fof(f412,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f401,f117])).

fof(f401,plain,
    ( k1_funct_1(sK0,k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))) = sK4(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_50 ),
    inference(resolution,[],[f397,f84])).

fof(f397,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f396])).

fof(f453,plain,
    ( spl6_54
    | spl6_9
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f446,f197,f191,f170,f130,f451])).

fof(f170,plain,
    ( spl6_14
  <=> k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f446,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f445,f192])).

fof(f445,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f184,f198])).

fof(f184,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f179,f131])).

fof(f179,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0)),k2_relat_1(sK0))
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_14 ),
    inference(superposition,[],[f76,f171])).

fof(f171,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f398,plain,
    ( spl6_50
    | spl6_9
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f391,f197,f191,f170,f130,f396])).

fof(f391,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f390,f192])).

fof(f390,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f183,f198])).

fof(f183,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f178,f131])).

fof(f178,plain,
    ( r2_hidden(sK4(k2_funct_1(sK0)),k2_relat_1(sK0))
    | v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_14 ),
    inference(superposition,[],[f77,f171])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f345,plain,
    ( spl6_42
    | spl6_9
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f304,f197,f191,f130,f343])).

fof(f304,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f303,f192])).

fof(f303,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f156,f198])).

fof(f156,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0))) = k1_funct_1(k2_funct_1(sK0),sK4(k2_funct_1(sK0)))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_9 ),
    inference(resolution,[],[f78,f131])).

fof(f78,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f225,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f223,f103])).

fof(f223,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f221,f110])).

fof(f221,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_19 ),
    inference(resolution,[],[f201,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',dt_k2_funct_1)).

fof(f201,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_19
  <=> ~ v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f216,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f214,f103])).

fof(f214,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f212,f110])).

fof(f212,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_17 ),
    inference(resolution,[],[f195,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f195,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_17
  <=> ~ v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f172,plain,
    ( spl6_14
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f165,f116,f109,f102,f170])).

fof(f165,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f164,f103])).

fof(f164,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f161,f110])).

fof(f161,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f160,f117])).

fof(f160,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f159,f59])).

fof(f159,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f97,f60])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
                  | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
              | ( ( k1_funct_1(X0,sK2(X0,X1)) != sK1(X0,X1)
                  | ~ r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                & k1_funct_1(X1,sK1(X0,X1)) = sK2(X0,X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f45])).

fof(f45,plain,(
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
     => ( ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
            | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
          & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
        | ( ( k1_funct_1(X0,sK2(X0,X1)) != sK1(X0,X1)
            | ~ r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          & k1_funct_1(X1,sK1(X0,X1)) = sK2(X0,X1)
          & r2_hidden(sK1(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',t54_funct_1)).

fof(f132,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f56,f130])).

fof(f56,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f40])).

fof(f40,plain,
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

fof(f22,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',t62_funct_1)).

fof(f118,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
