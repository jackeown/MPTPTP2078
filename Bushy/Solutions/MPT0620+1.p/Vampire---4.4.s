%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t15_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 6.70s
% Output     : Refutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 293 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   27
%              Number of atoms          :  390 (1613 expanded)
%              Number of equality atoms :  180 ( 719 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141551,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f141516,f141547,f141550])).

fof(f141550,plain,
    ( spl8_3
    | ~ spl8_698 ),
    inference(avatar_contradiction_clause,[],[f141549])).

fof(f141549,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_698 ),
    inference(subsumption_resolution,[],[f141548,f93])).

fof(f93,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_3
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f141548,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_698 ),
    inference(equality_resolution,[],[f141515])).

fof(f141515,plain,
    ( ! [X0] :
        ( sK0 != X0
        | k1_xboole_0 = X0 )
    | ~ spl8_698 ),
    inference(avatar_component_clause,[],[f141514])).

fof(f141514,plain,
    ( spl8_698
  <=> ! [X0] :
        ( sK0 != X0
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_698])])).

fof(f141547,plain,(
    ~ spl8_696 ),
    inference(avatar_contradiction_clause,[],[f141527])).

fof(f141527,plain,
    ( $false
    | ~ spl8_696 ),
    inference(unit_resulting_resolution,[],[f79,f141512,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',d1_tarski)).

fof(f141512,plain,
    ( ! [X1] : k1_tarski(sK1) != k1_tarski(X1)
    | ~ spl8_696 ),
    inference(avatar_component_clause,[],[f141511])).

fof(f141511,plain,
    ( spl8_696
  <=> ! [X1] : k1_tarski(sK1) != k1_tarski(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_696])])).

fof(f79,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f141516,plain,
    ( spl8_696
    | spl8_698 ),
    inference(avatar_split_clause,[],[f141365,f141514,f141511])).

fof(f141365,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != k1_tarski(X1)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f139400,f72])).

fof(f72,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK7(X0,X1)) = X0
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK7(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK7(X0,X1)) = X0
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',s3_funct_1__e2_24__funct_1)).

fof(f139400,plain,(
    ! [X3606,X3605] :
      ( k1_relat_1(sK7(X3605,X3606)) != sK0
      | k1_tarski(sK1) != k1_tarski(X3606)
      | k1_xboole_0 = X3605 ) ),
    inference(subsumption_resolution,[],[f139399,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f139399,plain,(
    ! [X3606,X3605] :
      ( k1_tarski(sK1) != k1_tarski(X3606)
      | k1_relat_1(sK7(X3605,X3606)) != sK0
      | ~ v1_relat_1(sK7(X3605,X3606))
      | k1_xboole_0 = X3605 ) ),
    inference(subsumption_resolution,[],[f139123,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f139123,plain,(
    ! [X3606,X3605] :
      ( k1_tarski(sK1) != k1_tarski(X3606)
      | k1_relat_1(sK7(X3605,X3606)) != sK0
      | ~ v1_funct_1(sK7(X3605,X3606))
      | ~ v1_relat_1(sK7(X3605,X3606))
      | k1_xboole_0 = X3605 ) ),
    inference(superposition,[],[f50,f138304])).

fof(f138304,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK7(X0,X1)) = k1_tarski(X1)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f135235])).

fof(f135235,plain,(
    ! [X72,X71,X73] :
      ( X72 != X73
      | k2_relat_1(sK7(X71,X72)) = k1_tarski(X73)
      | k1_xboole_0 = X71 ) ),
    inference(resolution,[],[f135170,f661])).

fof(f661,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(sK7(X1,X0)))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f659,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',t6_boole)).

fof(f659,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(sK7(X1,X0)))
      | k1_xboole_0 = X1
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f450,f120])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(o_1_0_funct_1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',dt_o_1_0_funct_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',t2_subset)).

fof(f450,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(o_1_0_funct_1(X2),X2)
      | r2_hidden(X3,k2_relat_1(sK7(X2,X3)))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f138,f276])).

fof(f276,plain,(
    ! [X6,X7] :
      ( k1_funct_1(sK7(X6,X7),o_1_0_funct_1(X6)) = X7
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f127,f53])).

fof(f127,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | k1_funct_1(sK7(X2,X3),o_1_0_funct_1(X2)) = X3 ) ),
    inference(resolution,[],[f73,f120])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK7(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(sK7(X1,X2),X0),k2_relat_1(sK7(X1,X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f137,f72])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK7(X1,X2)))
      | r2_hidden(k1_funct_1(sK7(X1,X2),X0),k2_relat_1(sK7(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f136,f70])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK7(X1,X2)))
      | r2_hidden(k1_funct_1(sK7(X1,X2),X0),k2_relat_1(sK7(X1,X2)))
      | ~ v1_relat_1(sK7(X1,X2)) ) ),
    inference(resolution,[],[f75,f71])).

fof(f75,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).

fof(f37,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',d5_funct_1)).

fof(f135170,plain,(
    ! [X26,X24,X25] :
      ( ~ r2_hidden(X26,k2_relat_1(sK7(X25,X26)))
      | k2_relat_1(sK7(X25,X26)) = k1_tarski(X24)
      | X24 != X26 ) ),
    inference(duplicate_literal_removal,[],[f135089])).

fof(f135089,plain,(
    ! [X26,X24,X25] :
      ( ~ r2_hidden(X26,k2_relat_1(sK7(X25,X26)))
      | k2_relat_1(sK7(X25,X26)) = k1_tarski(X24)
      | X24 != X26
      | X24 != X26
      | k2_relat_1(sK7(X25,X26)) = k1_tarski(X24) ) ),
    inference(superposition,[],[f12659,f12599])).

fof(f12599,plain,(
    ! [X2,X0,X1] :
      ( sK6(X0,k2_relat_1(sK7(X1,X2))) = X2
      | X0 != X2
      | k2_relat_1(sK7(X1,X2)) = k1_tarski(X0) ) ),
    inference(equality_factoring,[],[f2442])).

fof(f2442,plain,(
    ! [X2,X0,X1] :
      ( sK6(X2,k2_relat_1(sK7(X0,X1))) = X1
      | sK6(X2,k2_relat_1(sK7(X0,X1))) = X2
      | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2) ) ),
    inference(duplicate_literal_removal,[],[f2437])).

fof(f2437,plain,(
    ! [X2,X0,X1] :
      ( sK6(X2,k2_relat_1(sK7(X0,X1))) = X1
      | sK6(X2,k2_relat_1(sK7(X0,X1))) = X2
      | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2)
      | sK6(X2,k2_relat_1(sK7(X0,X1))) = X2
      | k2_relat_1(sK7(X0,X1)) = k1_tarski(X2) ) ),
    inference(superposition,[],[f219,f426])).

fof(f426,plain,(
    ! [X43,X41,X44,X42] :
      ( k1_funct_1(sK7(X41,X42),sK4(sK7(X41,X43),sK6(X44,k2_relat_1(sK7(X41,X43))))) = X42
      | sK6(X44,k2_relat_1(sK7(X41,X43))) = X44
      | k2_relat_1(sK7(X41,X43)) = k1_tarski(X44) ) ),
    inference(resolution,[],[f176,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | k1_funct_1(sK7(X1,X3),sK4(sK7(X1,X2),X0)) = X3 ) ),
    inference(resolution,[],[f144,f73])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK7(X1,X2),X0),X1)
      | ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2))) ) ),
    inference(forward_demodulation,[],[f143,f72])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | r2_hidden(sK4(sK7(X1,X2),X0),k1_relat_1(sK7(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f142,f70])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | r2_hidden(sK4(sK7(X1,X2),X0),k1_relat_1(sK7(X1,X2)))
      | ~ v1_relat_1(sK7(X1,X2)) ) ),
    inference(resolution,[],[f77,f71])).

fof(f77,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f219,plain,(
    ! [X12,X13,X11] :
      ( k1_funct_1(sK7(X11,X12),sK4(sK7(X11,X12),sK6(X13,k2_relat_1(sK7(X11,X12))))) = sK6(X13,k2_relat_1(sK7(X11,X12)))
      | sK6(X13,k2_relat_1(sK7(X11,X12))) = X13
      | k2_relat_1(sK7(X11,X12)) = k1_tarski(X13) ) ),
    inference(resolution,[],[f149,f66])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | k1_funct_1(sK7(X1,X2),sK4(sK7(X1,X2),X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f148,f70])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK7(X1,X2)))
      | k1_funct_1(sK7(X1,X2),sK4(sK7(X1,X2),X0)) = X0
      | ~ v1_relat_1(sK7(X1,X2)) ) ),
    inference(resolution,[],[f76,f71])).

fof(f76,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12659,plain,(
    ! [X26,X27,X25] :
      ( ~ r2_hidden(sK6(X25,k2_relat_1(sK7(X26,X27))),k2_relat_1(sK7(X26,X27)))
      | k2_relat_1(sK7(X26,X27)) = k1_tarski(X25)
      | X25 != X27 ) ),
    inference(subsumption_resolution,[],[f12629,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12629,plain,(
    ! [X26,X27,X25] :
      ( X25 != X27
      | k2_relat_1(sK7(X26,X27)) = k1_tarski(X25)
      | ~ r2_hidden(sK6(X25,k2_relat_1(sK7(X26,X27))),k2_relat_1(sK7(X26,X27)))
      | sK6(X25,k2_relat_1(sK7(X26,X27))) = X25 ) ),
    inference(duplicate_literal_removal,[],[f12569])).

fof(f12569,plain,(
    ! [X26,X27,X25] :
      ( X25 != X27
      | k2_relat_1(sK7(X26,X27)) = k1_tarski(X25)
      | ~ r2_hidden(sK6(X25,k2_relat_1(sK7(X26,X27))),k2_relat_1(sK7(X26,X27)))
      | sK6(X25,k2_relat_1(sK7(X26,X27))) = X25
      | k2_relat_1(sK7(X26,X27)) = k1_tarski(X25) ) ),
    inference(superposition,[],[f67,f2442])).

fof(f50,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
          ! [X2] :
            ( k2_relat_1(X2) != k1_tarski(X1)
            | k1_relat_1(X2) != X0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != sK0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
     => ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(sK1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t15_funct_1.p',t15_funct_1)).

fof(f94,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f49,f92])).

fof(f49,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
