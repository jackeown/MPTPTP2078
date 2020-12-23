%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t95_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:06 EDT 2019

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 299 expanded)
%              Number of leaves         :   37 ( 105 expanded)
%              Depth                    :   17
%              Number of atoms          :  577 (1327 expanded)
%              Number of equality atoms :   81 ( 193 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f165,f366,f371,f416,f3092,f3145,f3401,f3806,f3919,f3986,f5917,f6160,f6296,f6312,f7119])).

fof(f7119,plain,
    ( spl12_3
    | ~ spl12_98 ),
    inference(avatar_contradiction_clause,[],[f7117])).

fof(f7117,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_98 ),
    inference(subsumption_resolution,[],[f6191,f7008])).

fof(f7008,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl12_98 ),
    inference(trivial_inequality_removal,[],[f6962])).

fof(f6962,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl12_98 ),
    inference(superposition,[],[f121,f6885])).

fof(f6885,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl12_98 ),
    inference(resolution,[],[f6772,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',t6_boole)).

fof(f6772,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl12_98 ),
    inference(duplicate_literal_removal,[],[f6764])).

fof(f6764,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)))
    | v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl12_98 ),
    inference(resolution,[],[f6434,f3286])).

fof(f3286,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(k3_xboole_0(X3,X2)),X2)
      | v1_xboole_0(k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f3175,f108])).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',commutativity_k3_xboole_0)).

fof(f3175,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(k3_xboole_0(X2,X3)),X2)
      | v1_xboole_0(k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f3099,f149])).

fof(f149,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
            | ~ r2_hidden(sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK11(X0,X1,X2),X1)
              & r2_hidden(sK11(X0,X1,X2),X0) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f84,f85])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
          | ~ r2_hidden(sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X1)
            & r2_hidden(sK11(X0,X1,X2),X0) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',d4_xboole_0)).

fof(f3099,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f113,f106])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',existence_m1_subset_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',t2_subset)).

fof(f6434,plain,
    ( ! [X63] :
        ( ~ r2_hidden(sK6(k3_xboole_0(k1_relat_1(sK1),X63)),sK0)
        | v1_xboole_0(k3_xboole_0(X63,k1_relat_1(sK1))) )
    | ~ spl12_98 ),
    inference(resolution,[],[f6313,f3302])).

fof(f3302,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(k3_xboole_0(X3,X2)),X3)
      | v1_xboole_0(k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f3176,f108])).

fof(f3176,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK6(k3_xboole_0(X4,X5)),X5)
      | v1_xboole_0(k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f3099,f148])).

fof(f148,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f6313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl12_98 ),
    inference(resolution,[],[f494,f146])).

fof(f146,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f76,f79,f78,f77])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',d4_relat_1)).

fof(f494,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(k4_tarski(X7,X8),sK1)
        | ~ r2_hidden(X7,sK0) )
    | ~ spl12_98 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl12_98
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X7,sK0)
        | ~ r2_hidden(k4_tarski(X7,X8),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_98])])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',d7_xboole_0)).

fof(f6191,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl12_3 ),
    inference(resolution,[],[f157,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',symmetry_r1_xboole_0)).

fof(f157,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl12_3
  <=> ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f6312,plain,
    ( ~ spl12_65
    | spl12_98
    | ~ spl12_76 ),
    inference(avatar_split_clause,[],[f6306,f412,f493,f357])).

fof(f357,plain,
    ( spl12_65
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_65])])).

fof(f412,plain,
    ( spl12_76
  <=> ! [X5,X4] :
        ( r2_hidden(k4_tarski(X4,X5),k1_xboole_0)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(k4_tarski(X4,X5),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_76])])).

fof(f6306,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK0)
        | ~ r2_hidden(k4_tarski(X10,X11),sK1)
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl12_76 ),
    inference(resolution,[],[f413,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',t7_boole)).

fof(f413,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k1_xboole_0)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(k4_tarski(X4,X5),sK1) )
    | ~ spl12_76 ),
    inference(avatar_component_clause,[],[f412])).

fof(f6296,plain,
    ( ~ spl12_71
    | spl12_76
    | ~ spl12_37
    | ~ spl12_0 ),
    inference(avatar_split_clause,[],[f6295,f160,f286,f412,f399])).

fof(f399,plain,
    ( spl12_71
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_71])])).

fof(f286,plain,
    ( spl12_37
  <=> ~ v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f160,plain,
    ( spl12_0
  <=> k7_relat_1(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f6295,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k1_xboole_0)
        | r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl12_0 ),
    inference(forward_demodulation,[],[f6278,f161])).

fof(f161,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f160])).

fof(f6278,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl12_0 ),
    inference(superposition,[],[f140,f161])).

fof(f140,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK4(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
                    & r2_hidden(sK4(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',d11_relat_1)).

fof(f6160,plain,
    ( ~ spl12_71
    | spl12_0
    | ~ spl12_192
    | ~ spl12_548 ),
    inference(avatar_split_clause,[],[f6154,f4564,f1172,f160,f399])).

fof(f1172,plain,
    ( spl12_192
  <=> ! [X3,X4] :
        ( r2_hidden(sK4(X3,X4,k1_xboole_0),X4)
        | ~ v1_relat_1(X3)
        | k7_relat_1(X3,X4) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_192])])).

fof(f4564,plain,
    ( spl12_548
  <=> ! [X0] :
        ( k7_relat_1(sK1,X0) = k1_xboole_0
        | ~ r2_hidden(sK4(sK1,X0,k1_xboole_0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_548])])).

fof(f6154,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | ~ v1_relat_1(sK1)
    | ~ spl12_192
    | ~ spl12_548 ),
    inference(duplicate_literal_removal,[],[f6131])).

fof(f6131,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,sK0) = k1_xboole_0
    | ~ spl12_192
    | ~ spl12_548 ),
    inference(resolution,[],[f4565,f1173])).

fof(f1173,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK4(X3,X4,k1_xboole_0),X4)
        | ~ v1_relat_1(X3)
        | k7_relat_1(X3,X4) = k1_xboole_0 )
    | ~ spl12_192 ),
    inference(avatar_component_clause,[],[f1172])).

fof(f4565,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0,k1_xboole_0),sK0)
        | k7_relat_1(sK1,X0) = k1_xboole_0 )
    | ~ spl12_548 ),
    inference(avatar_component_clause,[],[f4564])).

fof(f5917,plain,
    ( ~ spl12_71
    | spl12_548
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_194 ),
    inference(avatar_split_clause,[],[f5879,f1176,f193,f163,f4564,f399])).

fof(f163,plain,
    ( spl12_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f193,plain,
    ( spl12_6
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f1176,plain,
    ( spl12_194
  <=> ! [X5,X6] :
        ( r2_hidden(k4_tarski(sK4(X5,X6,k1_xboole_0),sK5(X5,X6,k1_xboole_0)),X5)
        | ~ v1_relat_1(X5)
        | k7_relat_1(X5,X6) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_194])])).

fof(f5879,plain,
    ( ! [X43] :
        ( ~ r2_hidden(sK4(sK1,X43,k1_xboole_0),sK0)
        | k7_relat_1(sK1,X43) = k1_xboole_0
        | ~ v1_relat_1(sK1) )
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_194 ),
    inference(resolution,[],[f3932,f4150])).

fof(f4150,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK4(X1,X2,k1_xboole_0),k1_relat_1(X1))
        | k7_relat_1(X1,X2) = k1_xboole_0
        | ~ v1_relat_1(X1) )
    | ~ spl12_194 ),
    inference(resolution,[],[f1177,f145])).

fof(f145,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f1177,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(sK4(X5,X6,k1_xboole_0),sK5(X5,X6,k1_xboole_0)),X5)
        | ~ v1_relat_1(X5)
        | k7_relat_1(X5,X6) = k1_xboole_0 )
    | ~ spl12_194 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f3932,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0) )
    | ~ spl12_2
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f1309,f194])).

fof(f194,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f1309,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl12_2 ),
    inference(superposition,[],[f147,f1304])).

fof(f1304,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl12_2 ),
    inference(resolution,[],[f164,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f164,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f163])).

fof(f147,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f3986,plain,
    ( ~ spl12_37
    | spl12_194
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f3951,f193,f1176,f286])).

fof(f3951,plain,
    ( ! [X8,X9] :
        ( r2_hidden(k4_tarski(sK4(X8,X9,k1_xboole_0),sK5(X8,X9,k1_xboole_0)),X8)
        | k7_relat_1(X8,X9) = k1_xboole_0
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X8) )
    | ~ spl12_6 ),
    inference(resolution,[],[f194,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f3919,plain,(
    ~ spl12_412 ),
    inference(avatar_contradiction_clause,[],[f3918])).

fof(f3918,plain,
    ( $false
    | ~ spl12_412 ),
    inference(subsumption_resolution,[],[f90,f3916])).

fof(f3916,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_412 ),
    inference(resolution,[],[f3400,f129])).

fof(f3400,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | ~ spl12_412 ),
    inference(avatar_component_clause,[],[f3399])).

fof(f3399,plain,
    ( spl12_412
  <=> r2_hidden(sK6(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_412])])).

fof(f90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',fc1_xboole_0)).

fof(f3806,plain,
    ( spl12_376
    | spl12_6
    | ~ spl12_410 ),
    inference(avatar_split_clause,[],[f3717,f3396,f193,f3057])).

fof(f3057,plain,
    ( spl12_376
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_376])])).

fof(f3396,plain,
    ( spl12_410
  <=> ! [X0] : v1_xboole_0(k3_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_410])])).

fof(f3717,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ v1_xboole_0(X1) )
    | ~ spl12_410 ),
    inference(resolution,[],[f3435,f129])).

fof(f3435,plain,
    ( ! [X6,X5] :
        ( r2_hidden(X6,X5)
        | ~ r2_hidden(X6,k1_xboole_0) )
    | ~ spl12_410 ),
    inference(superposition,[],[f148,f3408])).

fof(f3408,plain,
    ( ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)
    | ~ spl12_410 ),
    inference(resolution,[],[f3397,f105])).

fof(f3397,plain,
    ( ! [X0] : v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))
    | ~ spl12_410 ),
    inference(avatar_component_clause,[],[f3396])).

fof(f3401,plain,
    ( spl12_410
    | spl12_412 ),
    inference(avatar_split_clause,[],[f3389,f3399,f3396])).

fof(f3389,plain,(
    ! [X0] :
      ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f3286,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',t2_boole)).

fof(f3145,plain,
    ( ~ spl12_37
    | spl12_192
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f3119,f193,f1172,f286])).

fof(f3119,plain,
    ( ! [X8,X7] :
        ( r2_hidden(sK4(X7,X8,k1_xboole_0),X8)
        | k7_relat_1(X7,X8) = k1_xboole_0
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X7) )
    | ~ spl12_6 ),
    inference(resolution,[],[f194,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f3092,plain,(
    ~ spl12_376 ),
    inference(avatar_contradiction_clause,[],[f3090])).

fof(f3090,plain,
    ( $false
    | ~ spl12_376 ),
    inference(subsumption_resolution,[],[f90,f3058])).

fof(f3058,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl12_376 ),
    inference(avatar_component_clause,[],[f3057])).

fof(f416,plain,(
    spl12_71 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl12_71 ),
    inference(subsumption_resolution,[],[f87,f400])).

fof(f400,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl12_71 ),
    inference(avatar_component_clause,[],[f399])).

fof(f87,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k7_relat_1(sK1,sK0) != k1_xboole_0 )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k7_relat_1(sK1,sK0) = k1_xboole_0 )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f55])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) = k1_xboole_0 )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k7_relat_1(sK1,sK0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k7_relat_1(sK1,sK0) = k1_xboole_0 )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k7_relat_1(X1,X0) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',t95_relat_1)).

fof(f371,plain,(
    spl12_37 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f287,f369])).

fof(f369,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f90,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t95_relat_1.p',cc1_relat_1)).

fof(f287,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f286])).

fof(f366,plain,(
    spl12_65 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl12_65 ),
    inference(subsumption_resolution,[],[f90,f358])).

fof(f358,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_65 ),
    inference(avatar_component_clause,[],[f357])).

fof(f165,plain,
    ( spl12_0
    | spl12_2 ),
    inference(avatar_split_clause,[],[f88,f163,f160])).

fof(f88,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k7_relat_1(sK1,sK0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

fof(f158,plain,
    ( ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f89,f156,f153])).

fof(f153,plain,
    ( spl12_1
  <=> k7_relat_1(sK1,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f89,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k7_relat_1(sK1,sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
