%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:38 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 418 expanded)
%              Number of leaves         :   33 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  822 (1934 expanded)
%              Number of equality atoms :   83 ( 219 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f108,f145,f151,f159,f169,f528,f538,f716,f785,f799,f826,f931,f940,f1033,f1042,f1112,f1137,f1151])).

fof(f1151,plain,
    ( spl4_7
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_97 ),
    inference(avatar_contradiction_clause,[],[f1150])).

fof(f1150,plain,
    ( $false
    | spl4_7
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f1149,f135])).

fof(f135,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_11
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1149,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7
    | ~ spl4_12
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f1148,f139])).

fof(f139,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_12
  <=> v1_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1148,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f1146,f81])).

fof(f81,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_7
  <=> v2_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1146,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_97 ),
    inference(trivial_inequality_removal,[],[f1144])).

fof(f1144,plain,
    ( sK2(k5_relat_1(sK0,sK1)) != sK2(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_97 ),
    inference(superposition,[],[f40,f1136])).

fof(f1136,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ spl4_97 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1134,plain,
    ( spl4_97
  <=> sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f40,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).

fof(f25,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f1137,plain,
    ( spl4_97
    | ~ spl4_65
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f1120,f1107,f796,f1134])).

fof(f796,plain,
    ( spl4_65
  <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1107,plain,
    ( spl4_94
  <=> ! [X1] :
        ( k1_funct_1(sK0,X1) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1120,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ spl4_65
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1119,f798])).

fof(f798,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f796])).

fof(f1119,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_94 ),
    inference(equality_resolution,[],[f1108])).

fof(f1108,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK0)) )
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f1112,plain,
    ( spl4_94
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_41
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1068,f1026,f535,f69,f54,f49,f1107])).

fof(f49,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f54,plain,
    ( spl4_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f69,plain,
    ( spl4_5
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f535,plain,
    ( spl4_41
  <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1026,plain,
    ( spl4_88
  <=> k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1068,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_41
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1067,f51])).

fof(f51,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f1067,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_41
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1066,f56])).

fof(f56,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f1066,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_5
    | ~ spl4_41
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1065,f71])).

fof(f71,plain,
    ( v2_funct_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1065,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_41
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1056,f537])).

fof(f537,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f535])).

fof(f1056,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_88 ),
    inference(superposition,[],[f36,f1028])).

fof(f1028,plain,
    ( k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f1026])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1042,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_63
    | spl4_89 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_63
    | spl4_89 ),
    inference(subsumption_resolution,[],[f1040,f61])).

fof(f61,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1040,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_63
    | spl4_89 ),
    inference(subsumption_resolution,[],[f1039,f66])).

fof(f66,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1039,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_63
    | spl4_89 ),
    inference(subsumption_resolution,[],[f1038,f51])).

fof(f1038,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_63
    | spl4_89 ),
    inference(subsumption_resolution,[],[f1037,f56])).

fof(f1037,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_63
    | spl4_89 ),
    inference(subsumption_resolution,[],[f1035,f773])).

fof(f773,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f772])).

fof(f772,plain,
    ( spl4_63
  <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f1035,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_89 ),
    inference(resolution,[],[f1032,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f1032,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | spl4_89 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1030,plain,
    ( spl4_89
  <=> r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f1033,plain,
    ( spl4_88
    | ~ spl4_89
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f954,f929,f1030,f1026])).

fof(f929,plain,
    ( spl4_82
  <=> ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f954,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
    | ~ spl4_82 ),
    inference(equality_resolution,[],[f930])).

fof(f930,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1 )
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f929])).

fof(f940,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_39
    | spl4_81 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_39
    | spl4_81 ),
    inference(subsumption_resolution,[],[f938,f61])).

fof(f938,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_39
    | spl4_81 ),
    inference(subsumption_resolution,[],[f937,f66])).

fof(f937,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39
    | spl4_81 ),
    inference(subsumption_resolution,[],[f936,f51])).

fof(f936,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_39
    | spl4_81 ),
    inference(subsumption_resolution,[],[f935,f56])).

fof(f935,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_39
    | spl4_81 ),
    inference(subsumption_resolution,[],[f933,f516])).

fof(f516,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl4_39
  <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f933,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_81 ),
    inference(resolution,[],[f927,f45])).

fof(f927,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | spl4_81 ),
    inference(avatar_component_clause,[],[f925])).

fof(f925,plain,
    ( spl4_81
  <=> r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f931,plain,
    ( ~ spl4_81
    | spl4_82
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f835,f823,f74,f64,f59,f929,f925])).

fof(f74,plain,
    ( spl4_6
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f823,plain,
    ( spl4_68
  <=> k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f835,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f834,f61])).

fof(f834,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f833,f66])).

fof(f833,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(subsumption_resolution,[],[f828,f76])).

fof(f76,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f828,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_68 ),
    inference(superposition,[],[f36,f825])).

fof(f825,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f823])).

fof(f826,plain,
    ( spl4_68
    | ~ spl4_14
    | ~ spl4_55
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f811,f796,f713,f167,f823])).

fof(f167,plain,
    ( spl4_14
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f713,plain,
    ( spl4_55
  <=> k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f811,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl4_14
    | ~ spl4_55
    | ~ spl4_65 ),
    inference(backward_demodulation,[],[f715,f805])).

fof(f805,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl4_14
    | ~ spl4_65 ),
    inference(resolution,[],[f798,f168])).

fof(f168,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f715,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f713])).

fof(f799,plain,
    ( spl4_65
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f794,f772,f64,f59,f54,f49,f796])).

fof(f794,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f793,f61])).

fof(f793,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f792,f66])).

fof(f792,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f791,f51])).

fof(f791,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f788,f56])).

fof(f788,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_63 ),
    inference(resolution,[],[f773,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f785,plain,
    ( spl4_7
    | ~ spl4_11
    | ~ spl4_12
    | spl4_63 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | spl4_7
    | ~ spl4_11
    | ~ spl4_12
    | spl4_63 ),
    inference(subsumption_resolution,[],[f783,f135])).

fof(f783,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7
    | ~ spl4_12
    | spl4_63 ),
    inference(subsumption_resolution,[],[f782,f139])).

fof(f782,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7
    | spl4_63 ),
    inference(subsumption_resolution,[],[f780,f81])).

fof(f780,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_63 ),
    inference(resolution,[],[f774,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f774,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl4_63 ),
    inference(avatar_component_clause,[],[f772])).

fof(f716,plain,
    ( spl4_55
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f704,f535,f167,f142,f713])).

fof(f142,plain,
    ( spl4_13
  <=> k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f704,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_41 ),
    inference(backward_demodulation,[],[f144,f544])).

fof(f544,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl4_14
    | ~ spl4_41 ),
    inference(resolution,[],[f537,f168])).

fof(f144,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f538,plain,
    ( spl4_41
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f533,f515,f64,f59,f54,f49,f535])).

fof(f533,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f532,f61])).

fof(f532,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f531,f66])).

fof(f531,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f530,f51])).

fof(f530,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f529,f56])).

fof(f529,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_39 ),
    inference(resolution,[],[f516,f44])).

fof(f528,plain,
    ( spl4_7
    | ~ spl4_11
    | ~ spl4_12
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl4_7
    | ~ spl4_11
    | ~ spl4_12
    | spl4_39 ),
    inference(subsumption_resolution,[],[f526,f135])).

fof(f526,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7
    | ~ spl4_12
    | spl4_39 ),
    inference(subsumption_resolution,[],[f525,f139])).

fof(f525,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7
    | spl4_39 ),
    inference(subsumption_resolution,[],[f523,f81])).

fof(f523,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_39 ),
    inference(resolution,[],[f517,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f517,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f515])).

fof(f169,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f121,f106,f64,f59,f167])).

fof(f106,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f121,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f118,f61])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f107,f66])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f159,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f157,f51])).

fof(f157,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f156,f56])).

fof(f156,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f155,f61])).

fof(f155,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f153,f66])).

fof(f153,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl4_12 ),
    inference(resolution,[],[f140,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f140,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f151,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_11 ),
    inference(subsumption_resolution,[],[f149,f51])).

fof(f149,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl4_3
    | spl4_11 ),
    inference(subsumption_resolution,[],[f147,f61])).

fof(f147,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl4_11 ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f136,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f145,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | spl4_7 ),
    inference(avatar_split_clause,[],[f83,f79,f142,f138,f134])).

fof(f83,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_7 ),
    inference(resolution,[],[f39,f81])).

fof(f39,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f102,f54,f49,f106])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0)) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f99,f51])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f43,f56])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f82,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    ~ v2_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    & v2_funct_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X1] :
        ( ~ v2_funct_1(k5_relat_1(sK0,X1))
        & v2_funct_1(X1)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
      & v2_funct_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f77,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (23380)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (23383)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (23375)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23375)Refutation not found, incomplete strategy% (23375)------------------------------
% 0.21/0.51  % (23375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23375)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23375)Memory used [KB]: 10618
% 0.21/0.51  % (23375)Time elapsed: 0.096 s
% 0.21/0.51  % (23375)------------------------------
% 0.21/0.51  % (23375)------------------------------
% 0.21/0.51  % (23395)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (23389)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (23391)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (23379)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (23385)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (23381)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (23377)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (23378)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (23384)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (23387)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23374)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (23388)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (23392)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (23394)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (23398)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (23382)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (23386)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (23390)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (23396)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (23397)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (23376)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (23399)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (23393)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.88/0.61  % (23376)Refutation found. Thanks to Tanya!
% 1.88/0.61  % SZS status Theorem for theBenchmark
% 1.88/0.61  % SZS output start Proof for theBenchmark
% 1.88/0.61  fof(f1152,plain,(
% 1.88/0.61    $false),
% 1.88/0.61    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f108,f145,f151,f159,f169,f528,f538,f716,f785,f799,f826,f931,f940,f1033,f1042,f1112,f1137,f1151])).
% 1.88/0.61  fof(f1151,plain,(
% 1.88/0.61    spl4_7 | ~spl4_11 | ~spl4_12 | ~spl4_97),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f1150])).
% 1.88/0.61  fof(f1150,plain,(
% 1.88/0.61    $false | (spl4_7 | ~spl4_11 | ~spl4_12 | ~spl4_97)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1149,f135])).
% 1.88/0.61  fof(f135,plain,(
% 1.88/0.61    v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl4_11),
% 1.88/0.61    inference(avatar_component_clause,[],[f134])).
% 1.88/0.61  fof(f134,plain,(
% 1.88/0.61    spl4_11 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.88/0.61  fof(f1149,plain,(
% 1.88/0.61    ~v1_relat_1(k5_relat_1(sK0,sK1)) | (spl4_7 | ~spl4_12 | ~spl4_97)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1148,f139])).
% 1.88/0.61  fof(f139,plain,(
% 1.88/0.61    v1_funct_1(k5_relat_1(sK0,sK1)) | ~spl4_12),
% 1.88/0.61    inference(avatar_component_clause,[],[f138])).
% 1.88/0.61  fof(f138,plain,(
% 1.88/0.61    spl4_12 <=> v1_funct_1(k5_relat_1(sK0,sK1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.88/0.61  fof(f1148,plain,(
% 1.88/0.61    ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | (spl4_7 | ~spl4_97)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1146,f81])).
% 1.88/0.61  fof(f81,plain,(
% 1.88/0.61    ~v2_funct_1(k5_relat_1(sK0,sK1)) | spl4_7),
% 1.88/0.61    inference(avatar_component_clause,[],[f79])).
% 1.88/0.61  fof(f79,plain,(
% 1.88/0.61    spl4_7 <=> v2_funct_1(k5_relat_1(sK0,sK1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.88/0.61  fof(f1146,plain,(
% 1.88/0.61    v2_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl4_97),
% 1.88/0.61    inference(trivial_inequality_removal,[],[f1144])).
% 1.88/0.61  fof(f1144,plain,(
% 1.88/0.61    sK2(k5_relat_1(sK0,sK1)) != sK2(k5_relat_1(sK0,sK1)) | v2_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl4_97),
% 1.88/0.61    inference(superposition,[],[f40,f1136])).
% 1.88/0.61  fof(f1136,plain,(
% 1.88/0.61    sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1)) | ~spl4_97),
% 1.88/0.61    inference(avatar_component_clause,[],[f1134])).
% 1.88/0.61  fof(f1134,plain,(
% 1.88/0.61    spl4_97 <=> sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 1.88/0.61  fof(f40,plain,(
% 1.88/0.61    ( ! [X0] : (sK2(X0) != sK3(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f26])).
% 1.88/0.61  fof(f26,plain,(
% 1.88/0.61    ! [X0] : (((v2_funct_1(X0) | (sK2(X0) != sK3(X0) & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).
% 1.88/0.61  fof(f25,plain,(
% 1.88/0.61    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK2(X0) != sK3(X0) & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) & r2_hidden(sK3(X0),k1_relat_1(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0))))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f24,plain,(
% 1.88/0.61    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/0.61    inference(rectify,[],[f23])).
% 1.88/0.61  fof(f23,plain,(
% 1.88/0.61    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/0.61    inference(nnf_transformation,[],[f11])).
% 1.88/0.61  fof(f11,plain,(
% 1.88/0.61    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/0.61    inference(flattening,[],[f10])).
% 1.88/0.61  fof(f10,plain,(
% 1.88/0.61    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f2])).
% 1.88/0.61  fof(f2,axiom,(
% 1.88/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.88/0.61  fof(f1137,plain,(
% 1.88/0.61    spl4_97 | ~spl4_65 | ~spl4_94),
% 1.88/0.61    inference(avatar_split_clause,[],[f1120,f1107,f796,f1134])).
% 1.88/0.61  fof(f796,plain,(
% 1.88/0.61    spl4_65 <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.88/0.61  fof(f1107,plain,(
% 1.88/0.61    spl4_94 <=> ! [X1] : (k1_funct_1(sK0,X1) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X1 | ~r2_hidden(X1,k1_relat_1(sK0)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 1.88/0.61  fof(f1120,plain,(
% 1.88/0.61    sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1)) | (~spl4_65 | ~spl4_94)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1119,f798])).
% 1.88/0.61  fof(f798,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~spl4_65),
% 1.88/0.61    inference(avatar_component_clause,[],[f796])).
% 1.88/0.61  fof(f1119,plain,(
% 1.88/0.61    sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1)) | ~r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~spl4_94),
% 1.88/0.61    inference(equality_resolution,[],[f1108])).
% 1.88/0.61  fof(f1108,plain,(
% 1.88/0.61    ( ! [X1] : (k1_funct_1(sK0,X1) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X1 | ~r2_hidden(X1,k1_relat_1(sK0))) ) | ~spl4_94),
% 1.88/0.61    inference(avatar_component_clause,[],[f1107])).
% 1.88/0.61  fof(f1112,plain,(
% 1.88/0.61    spl4_94 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_41 | ~spl4_88),
% 1.88/0.61    inference(avatar_split_clause,[],[f1068,f1026,f535,f69,f54,f49,f1107])).
% 1.88/0.61  fof(f49,plain,(
% 1.88/0.61    spl4_1 <=> v1_relat_1(sK0)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.88/0.61  fof(f54,plain,(
% 1.88/0.61    spl4_2 <=> v1_funct_1(sK0)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.88/0.61  fof(f69,plain,(
% 1.88/0.61    spl4_5 <=> v2_funct_1(sK0)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.88/0.61  fof(f535,plain,(
% 1.88/0.61    spl4_41 <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.88/0.61  fof(f1026,plain,(
% 1.88/0.61    spl4_88 <=> k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 1.88/0.61  fof(f1068,plain,(
% 1.88/0.61    ( ! [X2] : (k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X2 | ~r2_hidden(X2,k1_relat_1(sK0))) ) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_41 | ~spl4_88)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1067,f51])).
% 1.88/0.61  fof(f51,plain,(
% 1.88/0.61    v1_relat_1(sK0) | ~spl4_1),
% 1.88/0.61    inference(avatar_component_clause,[],[f49])).
% 1.88/0.61  fof(f1067,plain,(
% 1.88/0.61    ( ! [X2] : (k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X2 | ~r2_hidden(X2,k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl4_2 | ~spl4_5 | ~spl4_41 | ~spl4_88)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1066,f56])).
% 1.88/0.61  fof(f56,plain,(
% 1.88/0.61    v1_funct_1(sK0) | ~spl4_2),
% 1.88/0.61    inference(avatar_component_clause,[],[f54])).
% 1.88/0.61  fof(f1066,plain,(
% 1.88/0.61    ( ! [X2] : (k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X2 | ~r2_hidden(X2,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | (~spl4_5 | ~spl4_41 | ~spl4_88)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1065,f71])).
% 1.88/0.61  fof(f71,plain,(
% 1.88/0.61    v2_funct_1(sK0) | ~spl4_5),
% 1.88/0.61    inference(avatar_component_clause,[],[f69])).
% 1.88/0.61  fof(f1065,plain,(
% 1.88/0.61    ( ! [X2] : (k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X2 | ~r2_hidden(X2,k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | (~spl4_41 | ~spl4_88)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1056,f537])).
% 1.88/0.61  fof(f537,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~spl4_41),
% 1.88/0.61    inference(avatar_component_clause,[],[f535])).
% 1.88/0.61  fof(f1056,plain,(
% 1.88/0.61    ( ! [X2] : (k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | sK3(k5_relat_1(sK0,sK1)) = X2 | ~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | ~spl4_88),
% 1.88/0.61    inference(superposition,[],[f36,f1028])).
% 1.88/0.61  fof(f1028,plain,(
% 1.88/0.61    k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | ~spl4_88),
% 1.88/0.61    inference(avatar_component_clause,[],[f1026])).
% 1.88/0.61  fof(f36,plain,(
% 1.88/0.61    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f26])).
% 1.88/0.61  fof(f1042,plain,(
% 1.88/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_63 | spl4_89),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f1041])).
% 1.88/0.61  fof(f1041,plain,(
% 1.88/0.61    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_63 | spl4_89)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1040,f61])).
% 1.88/0.61  fof(f61,plain,(
% 1.88/0.61    v1_relat_1(sK1) | ~spl4_3),
% 1.88/0.61    inference(avatar_component_clause,[],[f59])).
% 1.88/0.61  fof(f59,plain,(
% 1.88/0.61    spl4_3 <=> v1_relat_1(sK1)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.88/0.61  fof(f1040,plain,(
% 1.88/0.61    ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_63 | spl4_89)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1039,f66])).
% 1.88/0.61  fof(f66,plain,(
% 1.88/0.61    v1_funct_1(sK1) | ~spl4_4),
% 1.88/0.61    inference(avatar_component_clause,[],[f64])).
% 1.88/0.61  fof(f64,plain,(
% 1.88/0.61    spl4_4 <=> v1_funct_1(sK1)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.88/0.61  fof(f1039,plain,(
% 1.88/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_63 | spl4_89)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1038,f51])).
% 1.88/0.61  fof(f1038,plain,(
% 1.88/0.61    ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_63 | spl4_89)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1037,f56])).
% 1.88/0.61  fof(f1037,plain,(
% 1.88/0.61    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_63 | spl4_89)),
% 1.88/0.61    inference(subsumption_resolution,[],[f1035,f773])).
% 1.88/0.61  fof(f773,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl4_63),
% 1.88/0.61    inference(avatar_component_clause,[],[f772])).
% 1.88/0.61  fof(f772,plain,(
% 1.88/0.61    spl4_63 <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 1.88/0.61  fof(f1035,plain,(
% 1.88/0.61    ~r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_89),
% 1.88/0.61    inference(resolution,[],[f1032,f45])).
% 1.88/0.61  fof(f45,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f28])).
% 1.88/0.61  fof(f28,plain,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.88/0.61    inference(flattening,[],[f27])).
% 1.88/0.61  fof(f27,plain,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.88/0.61    inference(nnf_transformation,[],[f17])).
% 1.88/0.61  fof(f17,plain,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.88/0.61    inference(flattening,[],[f16])).
% 1.88/0.61  fof(f16,plain,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f4])).
% 1.88/0.61  fof(f4,axiom,(
% 1.88/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 1.88/0.61  fof(f1032,plain,(
% 1.88/0.61    ~r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | spl4_89),
% 1.88/0.61    inference(avatar_component_clause,[],[f1030])).
% 1.88/0.61  fof(f1030,plain,(
% 1.88/0.61    spl4_89 <=> r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 1.88/0.61  fof(f1033,plain,(
% 1.88/0.61    spl4_88 | ~spl4_89 | ~spl4_82),
% 1.88/0.61    inference(avatar_split_clause,[],[f954,f929,f1030,f1026])).
% 1.88/0.61  fof(f929,plain,(
% 1.88/0.61    spl4_82 <=> ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | ~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 1.88/0.61  fof(f954,plain,(
% 1.88/0.61    ~r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) | ~spl4_82),
% 1.88/0.61    inference(equality_resolution,[],[f930])).
% 1.88/0.61  fof(f930,plain,(
% 1.88/0.61    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | ~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1) ) | ~spl4_82),
% 1.88/0.61    inference(avatar_component_clause,[],[f929])).
% 1.88/0.61  fof(f940,plain,(
% 1.88/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_39 | spl4_81),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f939])).
% 1.88/0.61  fof(f939,plain,(
% 1.88/0.61    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_39 | spl4_81)),
% 1.88/0.61    inference(subsumption_resolution,[],[f938,f61])).
% 1.88/0.61  fof(f938,plain,(
% 1.88/0.61    ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_39 | spl4_81)),
% 1.88/0.61    inference(subsumption_resolution,[],[f937,f66])).
% 1.88/0.61  fof(f937,plain,(
% 1.88/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_39 | spl4_81)),
% 1.88/0.61    inference(subsumption_resolution,[],[f936,f51])).
% 1.88/0.61  fof(f936,plain,(
% 1.88/0.61    ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_39 | spl4_81)),
% 1.88/0.61    inference(subsumption_resolution,[],[f935,f56])).
% 1.88/0.61  fof(f935,plain,(
% 1.88/0.61    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_39 | spl4_81)),
% 1.88/0.61    inference(subsumption_resolution,[],[f933,f516])).
% 1.88/0.61  fof(f516,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl4_39),
% 1.88/0.61    inference(avatar_component_clause,[],[f515])).
% 1.88/0.61  fof(f515,plain,(
% 1.88/0.61    spl4_39 <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.88/0.61  fof(f933,plain,(
% 1.88/0.61    ~r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_81),
% 1.88/0.61    inference(resolution,[],[f927,f45])).
% 1.88/0.61  fof(f927,plain,(
% 1.88/0.61    ~r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | spl4_81),
% 1.88/0.61    inference(avatar_component_clause,[],[f925])).
% 1.88/0.61  fof(f925,plain,(
% 1.88/0.61    spl4_81 <=> r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 1.88/0.61  fof(f931,plain,(
% 1.88/0.61    ~spl4_81 | spl4_82 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_68),
% 1.88/0.61    inference(avatar_split_clause,[],[f835,f823,f74,f64,f59,f929,f925])).
% 1.88/0.61  fof(f74,plain,(
% 1.88/0.61    spl4_6 <=> v2_funct_1(sK1)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.88/0.61  fof(f823,plain,(
% 1.88/0.61    spl4_68 <=> k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.88/0.61  fof(f835,plain,(
% 1.88/0.61    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1 | ~r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_68)),
% 1.88/0.61    inference(subsumption_resolution,[],[f834,f61])).
% 1.88/0.61  fof(f834,plain,(
% 1.88/0.61    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1 | ~r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl4_4 | ~spl4_6 | ~spl4_68)),
% 1.88/0.61    inference(subsumption_resolution,[],[f833,f66])).
% 1.88/0.61  fof(f833,plain,(
% 1.88/0.61    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1 | ~r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl4_6 | ~spl4_68)),
% 1.88/0.61    inference(subsumption_resolution,[],[f828,f76])).
% 1.88/0.61  fof(f76,plain,(
% 1.88/0.61    v2_funct_1(sK1) | ~spl4_6),
% 1.88/0.61    inference(avatar_component_clause,[],[f74])).
% 1.88/0.61  fof(f828,plain,(
% 1.88/0.61    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X1 | ~r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl4_68),
% 1.88/0.61    inference(superposition,[],[f36,f825])).
% 1.88/0.61  fof(f825,plain,(
% 1.88/0.61    k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | ~spl4_68),
% 1.88/0.61    inference(avatar_component_clause,[],[f823])).
% 1.88/0.61  fof(f826,plain,(
% 1.88/0.61    spl4_68 | ~spl4_14 | ~spl4_55 | ~spl4_65),
% 1.88/0.61    inference(avatar_split_clause,[],[f811,f796,f713,f167,f823])).
% 1.88/0.61  fof(f167,plain,(
% 1.88/0.61    spl4_14 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.88/0.61  fof(f713,plain,(
% 1.88/0.61    spl4_55 <=> k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.88/0.61  fof(f811,plain,(
% 1.88/0.61    k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | (~spl4_14 | ~spl4_55 | ~spl4_65)),
% 1.88/0.61    inference(backward_demodulation,[],[f715,f805])).
% 1.88/0.61  fof(f805,plain,(
% 1.88/0.61    k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) | (~spl4_14 | ~spl4_65)),
% 1.88/0.61    inference(resolution,[],[f798,f168])).
% 1.88/0.61  fof(f168,plain,(
% 1.88/0.61    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))) ) | ~spl4_14),
% 1.88/0.61    inference(avatar_component_clause,[],[f167])).
% 1.88/0.61  fof(f715,plain,(
% 1.88/0.61    k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) | ~spl4_55),
% 1.88/0.61    inference(avatar_component_clause,[],[f713])).
% 1.88/0.61  fof(f799,plain,(
% 1.88/0.61    spl4_65 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_63),
% 1.88/0.61    inference(avatar_split_clause,[],[f794,f772,f64,f59,f54,f49,f796])).
% 1.88/0.61  fof(f794,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f793,f61])).
% 1.88/0.61  fof(f793,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f792,f66])).
% 1.88/0.61  fof(f792,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f791,f51])).
% 1.88/0.61  fof(f791,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f788,f56])).
% 1.88/0.61  fof(f788,plain,(
% 1.88/0.61    r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_63),
% 1.88/0.61    inference(resolution,[],[f773,f44])).
% 1.88/0.61  fof(f44,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f28])).
% 1.88/0.61  fof(f785,plain,(
% 1.88/0.61    spl4_7 | ~spl4_11 | ~spl4_12 | spl4_63),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f784])).
% 1.88/0.61  fof(f784,plain,(
% 1.88/0.61    $false | (spl4_7 | ~spl4_11 | ~spl4_12 | spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f783,f135])).
% 1.88/0.61  fof(f783,plain,(
% 1.88/0.61    ~v1_relat_1(k5_relat_1(sK0,sK1)) | (spl4_7 | ~spl4_12 | spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f782,f139])).
% 1.88/0.61  fof(f782,plain,(
% 1.88/0.61    ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | (spl4_7 | spl4_63)),
% 1.88/0.61    inference(subsumption_resolution,[],[f780,f81])).
% 1.88/0.61  fof(f780,plain,(
% 1.88/0.61    v2_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl4_63),
% 1.88/0.61    inference(resolution,[],[f774,f37])).
% 1.88/0.61  fof(f37,plain,(
% 1.88/0.61    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f26])).
% 1.88/0.61  fof(f774,plain,(
% 1.88/0.61    ~r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | spl4_63),
% 1.88/0.61    inference(avatar_component_clause,[],[f772])).
% 1.88/0.61  fof(f716,plain,(
% 1.88/0.61    spl4_55 | ~spl4_13 | ~spl4_14 | ~spl4_41),
% 1.88/0.61    inference(avatar_split_clause,[],[f704,f535,f167,f142,f713])).
% 1.88/0.61  fof(f142,plain,(
% 1.88/0.61    spl4_13 <=> k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.88/0.61  fof(f704,plain,(
% 1.88/0.61    k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) | (~spl4_13 | ~spl4_14 | ~spl4_41)),
% 1.88/0.61    inference(backward_demodulation,[],[f144,f544])).
% 1.88/0.61  fof(f544,plain,(
% 1.88/0.61    k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) | (~spl4_14 | ~spl4_41)),
% 1.88/0.61    inference(resolution,[],[f537,f168])).
% 1.88/0.61  fof(f144,plain,(
% 1.88/0.61    k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) | ~spl4_13),
% 1.88/0.61    inference(avatar_component_clause,[],[f142])).
% 1.88/0.61  fof(f538,plain,(
% 1.88/0.61    spl4_41 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_39),
% 1.88/0.61    inference(avatar_split_clause,[],[f533,f515,f64,f59,f54,f49,f535])).
% 1.88/0.61  fof(f533,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f532,f61])).
% 1.88/0.61  fof(f532,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f531,f66])).
% 1.88/0.61  fof(f531,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f530,f51])).
% 1.88/0.61  fof(f530,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f529,f56])).
% 1.88/0.61  fof(f529,plain,(
% 1.88/0.61    r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_39),
% 1.88/0.61    inference(resolution,[],[f516,f44])).
% 1.88/0.61  fof(f528,plain,(
% 1.88/0.61    spl4_7 | ~spl4_11 | ~spl4_12 | spl4_39),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f527])).
% 1.88/0.61  fof(f527,plain,(
% 1.88/0.61    $false | (spl4_7 | ~spl4_11 | ~spl4_12 | spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f526,f135])).
% 1.88/0.61  fof(f526,plain,(
% 1.88/0.61    ~v1_relat_1(k5_relat_1(sK0,sK1)) | (spl4_7 | ~spl4_12 | spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f525,f139])).
% 1.88/0.61  fof(f525,plain,(
% 1.88/0.61    ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | (spl4_7 | spl4_39)),
% 1.88/0.61    inference(subsumption_resolution,[],[f523,f81])).
% 1.88/0.61  fof(f523,plain,(
% 1.88/0.61    v2_funct_1(k5_relat_1(sK0,sK1)) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl4_39),
% 1.88/0.61    inference(resolution,[],[f517,f38])).
% 1.88/0.61  fof(f38,plain,(
% 1.88/0.61    ( ! [X0] : (r2_hidden(sK3(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f26])).
% 1.88/0.61  fof(f517,plain,(
% 1.88/0.61    ~r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | spl4_39),
% 1.88/0.61    inference(avatar_component_clause,[],[f515])).
% 1.88/0.61  fof(f169,plain,(
% 1.88/0.61    spl4_14 | ~spl4_3 | ~spl4_4 | ~spl4_8),
% 1.88/0.61    inference(avatar_split_clause,[],[f121,f106,f64,f59,f167])).
% 1.88/0.61  fof(f106,plain,(
% 1.88/0.61    spl4_8 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.88/0.61  fof(f121,plain,(
% 1.88/0.61    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))) ) | (~spl4_3 | ~spl4_4 | ~spl4_8)),
% 1.88/0.61    inference(subsumption_resolution,[],[f118,f61])).
% 1.88/0.61  fof(f118,plain,(
% 1.88/0.61    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))) ) | (~spl4_4 | ~spl4_8)),
% 1.88/0.61    inference(resolution,[],[f107,f66])).
% 1.88/0.61  fof(f107,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0))) ) | ~spl4_8),
% 1.88/0.61    inference(avatar_component_clause,[],[f106])).
% 1.88/0.61  fof(f159,plain,(
% 1.88/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_12),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f158])).
% 1.88/0.61  fof(f158,plain,(
% 1.88/0.61    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_12)),
% 1.88/0.61    inference(subsumption_resolution,[],[f157,f51])).
% 1.88/0.61  fof(f157,plain,(
% 1.88/0.61    ~v1_relat_1(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_12)),
% 1.88/0.61    inference(subsumption_resolution,[],[f156,f56])).
% 1.88/0.61  fof(f156,plain,(
% 1.88/0.61    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl4_3 | ~spl4_4 | spl4_12)),
% 1.88/0.61    inference(subsumption_resolution,[],[f155,f61])).
% 1.88/0.61  fof(f155,plain,(
% 1.88/0.61    ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl4_4 | spl4_12)),
% 1.88/0.61    inference(subsumption_resolution,[],[f153,f66])).
% 1.88/0.61  fof(f153,plain,(
% 1.88/0.61    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl4_12),
% 1.88/0.61    inference(resolution,[],[f140,f42])).
% 1.88/0.61  fof(f42,plain,(
% 1.88/0.61    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f13])).
% 1.88/0.61  fof(f13,plain,(
% 1.88/0.61    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/0.61    inference(flattening,[],[f12])).
% 1.88/0.61  fof(f12,plain,(
% 1.88/0.61    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f3])).
% 1.88/0.61  fof(f3,axiom,(
% 1.88/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.88/0.61  fof(f140,plain,(
% 1.88/0.61    ~v1_funct_1(k5_relat_1(sK0,sK1)) | spl4_12),
% 1.88/0.61    inference(avatar_component_clause,[],[f138])).
% 1.88/0.61  fof(f151,plain,(
% 1.88/0.61    ~spl4_1 | ~spl4_3 | spl4_11),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f150])).
% 1.88/0.61  fof(f150,plain,(
% 1.88/0.61    $false | (~spl4_1 | ~spl4_3 | spl4_11)),
% 1.88/0.61    inference(subsumption_resolution,[],[f149,f51])).
% 1.88/0.61  fof(f149,plain,(
% 1.88/0.61    ~v1_relat_1(sK0) | (~spl4_3 | spl4_11)),
% 1.88/0.61    inference(subsumption_resolution,[],[f147,f61])).
% 1.88/0.61  fof(f147,plain,(
% 1.88/0.61    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl4_11),
% 1.88/0.61    inference(resolution,[],[f136,f47])).
% 1.88/0.61  fof(f47,plain,(
% 1.88/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f19])).
% 1.88/0.61  fof(f19,plain,(
% 1.88/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.88/0.61    inference(flattening,[],[f18])).
% 1.88/0.61  fof(f18,plain,(
% 1.88/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f1])).
% 1.88/0.61  fof(f1,axiom,(
% 1.88/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.88/0.61  fof(f136,plain,(
% 1.88/0.61    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl4_11),
% 1.88/0.61    inference(avatar_component_clause,[],[f134])).
% 1.88/0.61  fof(f145,plain,(
% 1.88/0.61    ~spl4_11 | ~spl4_12 | spl4_13 | spl4_7),
% 1.88/0.61    inference(avatar_split_clause,[],[f83,f79,f142,f138,f134])).
% 1.88/0.61  fof(f83,plain,(
% 1.88/0.61    k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl4_7),
% 1.88/0.61    inference(resolution,[],[f39,f81])).
% 1.88/0.61  fof(f39,plain,(
% 1.88/0.61    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f26])).
% 1.88/0.61  fof(f108,plain,(
% 1.88/0.61    spl4_8 | ~spl4_1 | ~spl4_2),
% 1.88/0.61    inference(avatar_split_clause,[],[f102,f54,f49,f106])).
% 1.88/0.61  fof(f102,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0))) ) | (~spl4_1 | ~spl4_2)),
% 1.88/0.61    inference(subsumption_resolution,[],[f99,f51])).
% 1.88/0.61  fof(f99,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK0,X1),X0) = k1_funct_1(X1,k1_funct_1(sK0,X0)) | ~v1_relat_1(sK0)) ) | ~spl4_2),
% 1.88/0.61    inference(resolution,[],[f43,f56])).
% 1.88/0.61  fof(f43,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f15])).
% 1.88/0.61  fof(f15,plain,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.88/0.61    inference(flattening,[],[f14])).
% 1.88/0.61  fof(f14,plain,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f5])).
% 1.88/0.61  fof(f5,axiom,(
% 1.88/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.88/0.61  fof(f82,plain,(
% 1.88/0.61    ~spl4_7),
% 1.88/0.61    inference(avatar_split_clause,[],[f35,f79])).
% 1.88/0.61  fof(f35,plain,(
% 1.88/0.61    ~v2_funct_1(k5_relat_1(sK0,sK1))),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f22,plain,(
% 1.88/0.61    (~v2_funct_1(k5_relat_1(sK0,sK1)) & v2_funct_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).
% 1.88/0.61  fof(f20,plain,(
% 1.88/0.61    ? [X0] : (? [X1] : (~v2_funct_1(k5_relat_1(X0,X1)) & v2_funct_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_funct_1(k5_relat_1(sK0,X1)) & v2_funct_1(X1) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f21,plain,(
% 1.88/0.61    ? [X1] : (~v2_funct_1(k5_relat_1(sK0,X1)) & v2_funct_1(X1) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_funct_1(k5_relat_1(sK0,sK1)) & v2_funct_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f9,plain,(
% 1.88/0.61    ? [X0] : (? [X1] : (~v2_funct_1(k5_relat_1(X0,X1)) & v2_funct_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.88/0.61    inference(flattening,[],[f8])).
% 1.88/0.61  fof(f8,plain,(
% 1.88/0.61    ? [X0] : (? [X1] : ((~v2_funct_1(k5_relat_1(X0,X1)) & (v2_funct_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.88/0.61    inference(ennf_transformation,[],[f7])).
% 1.88/0.61  fof(f7,negated_conjecture,(
% 1.88/0.61    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.88/0.61    inference(negated_conjecture,[],[f6])).
% 1.88/0.61  fof(f6,conjecture,(
% 1.88/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 1.88/0.61  fof(f77,plain,(
% 1.88/0.61    spl4_6),
% 1.88/0.61    inference(avatar_split_clause,[],[f34,f74])).
% 1.88/0.61  fof(f34,plain,(
% 1.88/0.61    v2_funct_1(sK1)),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f72,plain,(
% 1.88/0.61    spl4_5),
% 1.88/0.61    inference(avatar_split_clause,[],[f33,f69])).
% 1.88/0.61  fof(f33,plain,(
% 1.88/0.61    v2_funct_1(sK0)),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f67,plain,(
% 1.88/0.61    spl4_4),
% 1.88/0.61    inference(avatar_split_clause,[],[f32,f64])).
% 1.88/0.61  fof(f32,plain,(
% 1.88/0.61    v1_funct_1(sK1)),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f62,plain,(
% 1.88/0.61    spl4_3),
% 1.88/0.61    inference(avatar_split_clause,[],[f31,f59])).
% 1.88/0.61  fof(f31,plain,(
% 1.88/0.61    v1_relat_1(sK1)),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f57,plain,(
% 1.88/0.61    spl4_2),
% 1.88/0.61    inference(avatar_split_clause,[],[f30,f54])).
% 1.88/0.61  fof(f30,plain,(
% 1.88/0.61    v1_funct_1(sK0)),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  fof(f52,plain,(
% 1.88/0.61    spl4_1),
% 1.88/0.61    inference(avatar_split_clause,[],[f29,f49])).
% 1.88/0.61  fof(f29,plain,(
% 1.88/0.61    v1_relat_1(sK0)),
% 1.88/0.61    inference(cnf_transformation,[],[f22])).
% 1.88/0.61  % SZS output end Proof for theBenchmark
% 1.88/0.61  % (23376)------------------------------
% 1.88/0.61  % (23376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (23376)Termination reason: Refutation
% 1.88/0.61  
% 1.88/0.61  % (23376)Memory used [KB]: 7036
% 1.88/0.61  % (23376)Time elapsed: 0.194 s
% 1.88/0.61  % (23376)------------------------------
% 1.88/0.61  % (23376)------------------------------
% 2.04/0.63  % (23373)Success in time 0.258 s
%------------------------------------------------------------------------------
