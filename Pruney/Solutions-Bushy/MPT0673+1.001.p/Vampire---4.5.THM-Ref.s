%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0673+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:25 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 370 expanded)
%              Number of leaves         :   23 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  530 (1746 expanded)
%              Number of equality atoms :   85 ( 265 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f85,f97,f102,f107,f136,f141,f147,f167,f172,f182,f204])).

fof(f204,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f199,f176])).

fof(f176,plain,
    ( k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_16
  <=> k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f199,plain,
    ( k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1))) != k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_6
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f73,f68,f63,f135,f96,f166,f36])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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

fof(f166,plain,
    ( r2_hidden(sK2(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_15
  <=> r2_hidden(sK2(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f96,plain,
    ( sK2(k8_relat_1(sK0,sK1)) != sK3(k8_relat_1(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_6
  <=> sK2(k8_relat_1(sK0,sK1)) = sK3(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f135,plain,
    ( r2_hidden(sK3(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_11
  <=> r2_hidden(sK3(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f63,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f68,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f73,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f182,plain,
    ( spl6_16
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f181,f154,f143,f174])).

fof(f143,plain,
    ( spl6_12
  <=> k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f154,plain,
    ( spl6_13
  <=> k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f181,plain,
    ( k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f145,f156])).

fof(f156,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f145,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f172,plain,
    ( spl6_13
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f171,f104,f71,f66,f154])).

fof(f104,plain,
    ( spl6_8
  <=> r2_hidden(sK2(k8_relat_1(sK0,sK1)),k1_relat_1(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f171,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f170,f77])).

fof(f77,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK1))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f73,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f170,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f169,f76])).

fof(f76,plain,
    ( ! [X0] : v1_funct_1(k8_relat_1(X0,sK1))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f68,f73,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f169,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f168,f73])).

fof(f168,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f152,f68])).

fof(f152,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK2(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X2,X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(k8_relat_1(X0,X2)))
      | k1_funct_1(X2,X5) = k1_funct_1(k8_relat_1(X0,X2),X5)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ( k1_funct_1(X2,sK4(X1,X2)) != k1_funct_1(X1,sK4(X1,X2))
                & r2_hidden(sK4(X1,X2),k1_relat_1(X1)) )
              | ( ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
                  | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X0)
                    & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
                  | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) ) ) )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X2,sK4(X1,X2)) != k1_funct_1(X1,sK4(X1,X2))
        & r2_hidden(sK4(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
            | ~ r2_hidden(X4,k1_relat_1(X2))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X1)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                      | ~ r2_hidden(X4,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                        & r2_hidden(X4,k1_relat_1(X2)) )
                      | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X1)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                      | ~ r2_hidden(X4,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                        & r2_hidden(X4,k1_relat_1(X2)) )
                      | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(f106,plain,
    ( r2_hidden(sK2(k8_relat_1(sK0,sK1)),k1_relat_1(k8_relat_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f167,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f149,f104,f71,f66,f164])).

fof(f149,plain,
    ( r2_hidden(sK2(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f73,f68,f77,f76,f106,f54])).

fof(f54,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f147,plain,
    ( spl6_12
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f146,f123,f82,f143])).

fof(f82,plain,
    ( spl6_5
  <=> k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f123,plain,
    ( spl6_9
  <=> k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f146,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f84,f125])).

fof(f125,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f84,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f141,plain,
    ( spl6_9
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f140,f99,f71,f66,f123])).

fof(f99,plain,
    ( spl6_7
  <=> r2_hidden(sK3(k8_relat_1(sK0,sK1)),k1_relat_1(k8_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f140,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f139,f77])).

fof(f139,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f138,f76])).

fof(f138,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f137,f73])).

fof(f137,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f121,f68])).

fof(f121,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1))) = k1_funct_1(sK1,sK3(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl6_7 ),
    inference(resolution,[],[f101,f51])).

fof(f101,plain,
    ( r2_hidden(sK3(k8_relat_1(sK0,sK1)),k1_relat_1(k8_relat_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f136,plain,
    ( spl6_11
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f118,f99,f71,f66,f133])).

fof(f118,plain,
    ( r2_hidden(sK3(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f73,f68,f77,f76,f101,f54])).

fof(f107,plain,
    ( spl6_8
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f89,f71,f66,f56,f104])).

fof(f56,plain,
    ( spl6_1
  <=> v2_funct_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f89,plain,
    ( r2_hidden(sK2(k8_relat_1(sK0,sK1)),k1_relat_1(k8_relat_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f58,f76,f77,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,
    ( ~ v2_funct_1(k8_relat_1(sK0,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f102,plain,
    ( spl6_7
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f90,f71,f66,f56,f99])).

fof(f90,plain,
    ( r2_hidden(sK3(k8_relat_1(sK0,sK1)),k1_relat_1(k8_relat_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f58,f76,f77,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,
    ( ~ spl6_6
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f92,f71,f66,f56,f94])).

fof(f92,plain,
    ( sK2(k8_relat_1(sK0,sK1)) != sK3(k8_relat_1(sK0,sK1))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f58,f76,f77,f40])).

fof(f40,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( spl6_5
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f80,f71,f66,f56,f82])).

fof(f80,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f79,f77])).

fof(f79,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f78,f76])).

fof(f78,plain,
    ( k1_funct_1(k8_relat_1(sK0,sK1),sK2(k8_relat_1(sK0,sK1))) = k1_funct_1(k8_relat_1(sK0,sK1),sK3(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_funct_1(k8_relat_1(sK0,sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k8_relat_1(X0,X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k8_relat_1(sK0,sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_funct_1)).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    ~ v2_funct_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
