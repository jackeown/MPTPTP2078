%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t28_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 129 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 757 expanded)
%              Number of equality atoms :   48 ( 137 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f141,f205,f1742,f2925,f3315,f3323])).

fof(f3323,plain,
    ( spl6_13
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f3318])).

fof(f3318,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_94 ),
    inference(unit_resulting_resolution,[],[f140,f3262])).

fof(f3262,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k2_wellord1(k2_wellord1(sK1,X0),X0)
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f3261])).

fof(f3261,plain,
    ( spl6_94
  <=> ! [X0] : k2_wellord1(sK1,X0) = k2_wellord1(k2_wellord1(sK1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f140,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_13
  <=> k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f3315,plain,
    ( spl6_94
    | ~ spl6_58
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f3096,f2923,f1740,f3261])).

fof(f1740,plain,
    ( spl6_58
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k3_xboole_0(k2_wellord1(sK1,X0),k2_zfmisc_1(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f2923,plain,
    ( spl6_90
  <=> ! [X11] : k2_wellord1(sK1,X11) = k3_xboole_0(k2_wellord1(sK1,X11),k2_zfmisc_1(X11,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f3096,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k2_wellord1(k2_wellord1(sK1,X0),X0)
    | ~ spl6_58
    | ~ spl6_90 ),
    inference(superposition,[],[f1741,f2924])).

fof(f2924,plain,
    ( ! [X11] : k2_wellord1(sK1,X11) = k3_xboole_0(k2_wellord1(sK1,X11),k2_zfmisc_1(X11,X11))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f2923])).

fof(f1741,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k3_xboole_0(k2_wellord1(sK1,X0),k2_zfmisc_1(X1,X1))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f1740])).

fof(f2925,plain,
    ( spl6_90
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f1314,f203,f2923])).

fof(f203,plain,
    ( spl6_16
  <=> ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1314,plain,
    ( ! [X11] : k2_wellord1(sK1,X11) = k3_xboole_0(k2_wellord1(sK1,X11),k2_zfmisc_1(X11,X11))
    | ~ spl6_16 ),
    inference(superposition,[],[f1183,f204])).

fof(f204,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1183,plain,(
    ! [X30,X29] : k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X29,X30),X30) ),
    inference(subsumption_resolution,[],[f1165,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X0),X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f219,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t28_wellord1.p',d4_xboole_0)).

fof(f219,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r2_hidden(sK5(X0,X1,X0),X1)
      | ~ r2_hidden(sK5(X0,X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r2_hidden(sK5(X0,X1,X0),X1)
      | ~ r2_hidden(sK5(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f172,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f70])).

fof(f1165,plain,(
    ! [X30,X29] :
      ( k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X29,X30),X30)
      | r2_hidden(sK5(k3_xboole_0(X29,X30),X30,k3_xboole_0(X29,X30)),X30) ) ),
    inference(duplicate_literal_removal,[],[f1157])).

fof(f1157,plain,(
    ! [X30,X29] :
      ( k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X29,X30),X30)
      | r2_hidden(sK5(k3_xboole_0(X29,X30),X30,k3_xboole_0(X29,X30)),X30)
      | k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X29,X30),X30) ) ),
    inference(resolution,[],[f220,f186])).

fof(f186,plain,(
    ! [X14,X17,X15,X16] :
      ( r2_hidden(sK5(X14,X15,k3_xboole_0(X16,X17)),X15)
      | r2_hidden(sK5(X14,X15,k3_xboole_0(X16,X17)),X17)
      | k3_xboole_0(X14,X15) = k3_xboole_0(X16,X17) ) ),
    inference(resolution,[],[f71,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1742,plain,
    ( spl6_58
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f254,f84,f1740])).

fof(f84,plain,
    ( spl6_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f254,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k3_xboole_0(k2_wellord1(sK1,X0),k2_zfmisc_1(X1,X1))
    | ~ spl6_0 ),
    inference(resolution,[],[f153,f85])).

fof(f85,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f153,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(k2_wellord1(X1,X2),X3) = k3_xboole_0(k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3)) ) ),
    inference(resolution,[],[f53,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t28_wellord1.p',dt_k2_wellord1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t28_wellord1.p',d6_wellord1)).

fof(f205,plain,
    ( spl6_16
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f152,f84,f203])).

fof(f152,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0))
    | ~ spl6_0 ),
    inference(resolution,[],[f53,f85])).

fof(f141,plain,(
    ~ spl6_13 ),
    inference(avatar_split_clause,[],[f49,f139])).

fof(f49,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t28_wellord1.p',t28_wellord1)).

fof(f86,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
