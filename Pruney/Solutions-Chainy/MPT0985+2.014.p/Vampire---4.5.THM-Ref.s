%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 948 expanded)
%              Number of leaves         :   35 ( 240 expanded)
%              Depth                    :   20
%              Number of atoms          :  774 (4764 expanded)
%              Number of equality atoms :  151 ( 888 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1499,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f166,f182,f656,f1005,f1014,f1022,f1078,f1093,f1117,f1291,f1470,f1498])).

fof(f1498,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f1496])).

fof(f1496,plain,
    ( $false
    | ~ spl6_7 ),
    inference(resolution,[],[f181,f72])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f181,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_7
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1470,plain,
    ( spl6_2
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1469])).

fof(f1469,plain,
    ( $false
    | spl6_2
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1460,f72])).

fof(f1460,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f1429,f1446])).

fof(f1446,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(resolution,[],[f287,f1350])).

fof(f1350,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_relat_1(k1_xboole_0))
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1349,f77])).

fof(f77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f1349,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1348,f78])).

fof(f78,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

fof(f1348,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_relat_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1345,f143])).

fof(f143,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f136,f72])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f135,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f135,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f86,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f1345,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_relat_1(k1_xboole_0))
        | ~ v2_funct_1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(superposition,[],[f1299,f92])).

fof(f92,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1299,plain,
    ( ! [X1] : ~ r2_hidden(X1,k2_funct_1(k1_xboole_0))
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f1001,f379])).

fof(f379,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1001,plain,
    ( ! [X1] : ~ r2_hidden(X1,k2_funct_1(sK2))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl6_30
  <=> ! [X1] : ~ r2_hidden(X1,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f287,plain,
    ( ! [X4] :
        ( r2_hidden(sK3(k1_xboole_0,X4),X4)
        | k1_xboole_0 = X4 )
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f285,f74])).

fof(f74,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f285,plain,
    ( ! [X4] :
        ( k2_relat_1(k1_xboole_0) = X4
        | r2_hidden(sK3(k1_xboole_0,X4),X4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f100,f178])).

fof(f178,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f177])).

% (21671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f177,plain,
    ( spl6_6
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f58,f61,f60,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1429,plain,
    ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
    | spl6_2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(resolution,[],[f506,f1334])).

fof(f1334,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1333,f77])).

fof(f1333,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1332,f78])).

fof(f1332,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1330,f143])).

fof(f1330,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(superposition,[],[f1312,f92])).

fof(f1312,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f1126,f379])).

fof(f1126,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f130,f301])).

fof(f301,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f130,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f506,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X0,k1_xboole_0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f505,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f76,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f505,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X0,k1_xboole_0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f499,f81])).

fof(f499,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X0,k1_xboole_0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f259,f146])).

fof(f146,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f73,f81])).

fof(f73,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f259,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f257,f119])).

fof(f119,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f257,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f139,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f139,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f123,f119])).

fof(f123,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1291,plain,
    ( spl6_2
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f1290])).

fof(f1290,plain,
    ( $false
    | spl6_2
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1288,f1280])).

fof(f1280,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f1126,f373])).

fof(f373,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1288,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f1038,f1285])).

fof(f1285,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f1281,f1058])).

fof(f1058,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1029,f118])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1029,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f244,f301])).

fof(f244,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(subsumption_resolution,[],[f243,f161])).

fof(f161,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f54])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f243,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f66])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f89,f240])).

fof(f240,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f238,f68])).

fof(f238,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f107,f70])).

fof(f70,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1281,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f1278,f266])).

fof(f266,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f261,f119])).

fof(f261,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f140,f106])).

fof(f140,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f124,f119])).

fof(f124,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1278,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f1023,f373])).

fof(f1023,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f67,f301])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f1038,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f653,f301])).

fof(f653,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f652,f161])).

fof(f652,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f651,f66])).

fof(f651,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f646,f69])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f646,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f621,f94])).

fof(f94,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f621,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f620,f161])).

fof(f620,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f619,f66])).

fof(f619,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f603,f69])).

fof(f603,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f219,f240])).

fof(f219,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f218,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f218,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f214,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f214,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f88,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1117,plain,
    ( spl6_3
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f1116])).

fof(f1116,plain,
    ( $false
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1056,f1086])).

fof(f1086,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1085,f72])).

fof(f1085,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1084,f301])).

fof(f1084,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f989,f301])).

fof(f989,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(sK1))
    | ~ v1_xboole_0(sK1) ),
    inference(superposition,[],[f720,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f119,f81])).

fof(f720,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f719,f161])).

fof(f719,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f718,f66])).

fof(f718,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f698,f69])).

% (21676)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f698,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f217,f240])).

fof(f217,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f216,f90])).

fof(f216,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f213,f91])).

fof(f213,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f89,f93])).

fof(f1056,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1026,f119])).

fof(f1026,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_3
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f133,f301])).

fof(f133,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1093,plain,
    ( spl6_14
    | spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f1092,f300,f372,f378])).

fof(f1092,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1091,f72])).

fof(f1091,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1090,f301])).

fof(f1090,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1089,f301])).

fof(f1089,plain,
    ( k1_xboole_0 = sK2
    | sK0 = sK1
    | ~ v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1088,f1058])).

fof(f1088,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | sK0 = sK1
    | ~ v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1087,f301])).

fof(f1087,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | sK0 = sK1
    | ~ v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f766,f301])).

fof(f766,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | sK0 = sK1
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f251,f67])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X2,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X2
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f138,f81])).

fof(f138,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f122,f118])).

fof(f122,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1078,plain,
    ( ~ spl6_10
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f1077])).

fof(f1077,plain,
    ( $false
    | ~ spl6_10
    | spl6_31 ),
    inference(subsumption_resolution,[],[f1076,f72])).

fof(f1076,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_10
    | spl6_31 ),
    inference(forward_demodulation,[],[f1048,f119])).

fof(f1048,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))
    | ~ spl6_10
    | spl6_31 ),
    inference(backward_demodulation,[],[f1004,f301])).

fof(f1004,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1003,plain,
    ( spl6_31
  <=> v1_xboole_0(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1022,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f1021,f300,f297])).

fof(f297,plain,
    ( spl6_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1021,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f333,f67])).

fof(f333,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f68,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1014,plain,
    ( spl6_3
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f1013])).

fof(f1013,plain,
    ( $false
    | spl6_3
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1012,f133])).

fof(f1012,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1011,f348])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f344,f68])).

fof(f344,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(superposition,[],[f298,f106])).

fof(f298,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f297])).

fof(f1011,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f1010,f161])).

fof(f1010,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1009,f66])).

fof(f1009,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f987,f69])).

fof(f987,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f720,f94])).

fof(f1005,plain,
    ( spl6_30
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f985,f1003,f1000])).

fof(f985,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))
      | ~ r2_hidden(X1,k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f720,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f656,plain,
    ( spl6_2
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f654,f130])).

fof(f654,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f653,f348])).

fof(f182,plain,
    ( spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f168,f180,f177])).

fof(f168,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f115,f76])).

fof(f166,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f161,f159])).

fof(f159,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f158,f66])).

fof(f158,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_1 ),
    inference(resolution,[],[f91,f127])).

fof(f127,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f134,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f71,f132,f129,f126])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (21666)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.45  % (21658)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (21673)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (21661)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (21668)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21660)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (21670)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (21657)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21662)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (21659)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (21675)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (21656)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (21658)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f1499,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f134,f166,f182,f656,f1005,f1014,f1022,f1078,f1093,f1117,f1291,f1470,f1498])).
% 0.20/0.50  fof(f1498,plain,(
% 0.20/0.50    ~spl6_7),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1496])).
% 0.20/0.50  fof(f1496,plain,(
% 0.20/0.50    $false | ~spl6_7),
% 0.20/0.50    inference(resolution,[],[f181,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl6_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    spl6_7 <=> ! [X1] : ~v1_xboole_0(X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.50  fof(f1470,plain,(
% 0.20/0.50    spl6_2 | ~spl6_6 | ~spl6_10 | ~spl6_14 | ~spl6_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1469])).
% 0.20/0.50  fof(f1469,plain,(
% 0.20/0.50    $false | (spl6_2 | ~spl6_6 | ~spl6_10 | ~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1460,f72])).
% 0.20/0.50  fof(f1460,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (spl6_2 | ~spl6_6 | ~spl6_10 | ~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(backward_demodulation,[],[f1429,f1446])).
% 0.20/0.50  fof(f1446,plain,(
% 0.20/0.50    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl6_6 | ~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(resolution,[],[f287,f1350])).
% 0.20/0.50  fof(f1350,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k4_relat_1(k1_xboole_0))) ) | (~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1349,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    v1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(rectify,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.20/0.50  fof(f1349,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1348,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    v1_funct_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f56])).
% 0.20/0.50  fof(f1348,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k4_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1345,f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    v2_funct_1(k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f136,f72])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f135,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f86,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).
% 0.20/0.50  fof(f1345,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k4_relat_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(superposition,[],[f1299,f92])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.50  fof(f1299,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,k2_funct_1(k1_xboole_0))) ) | (~spl6_14 | ~spl6_30)),
% 0.20/0.50    inference(backward_demodulation,[],[f1001,f379])).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~spl6_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f378])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    spl6_14 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.50  fof(f1001,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,k2_funct_1(sK2))) ) | ~spl6_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f1000])).
% 0.20/0.50  fof(f1000,plain,(
% 0.20/0.50    spl6_30 <=> ! [X1] : ~r2_hidden(X1,k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    ( ! [X4] : (r2_hidden(sK3(k1_xboole_0,X4),X4) | k1_xboole_0 = X4) ) | ~spl6_6),
% 0.20/0.50    inference(forward_demodulation,[],[f285,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    ( ! [X4] : (k2_relat_1(k1_xboole_0) = X4 | r2_hidden(sK3(k1_xboole_0,X4),X4)) ) | ~spl6_6),
% 0.20/0.50    inference(resolution,[],[f100,f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl6_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f177])).
% 0.20/0.50  % (21671)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    spl6_6 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f58,f61,f60,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.50    inference(rectify,[],[f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.50  fof(f1429,plain,(
% 0.20/0.50    ~v1_xboole_0(k4_relat_1(k1_xboole_0)) | (spl6_2 | ~spl6_10 | ~spl6_14)),
% 0.20/0.50    inference(resolution,[],[f506,f1334])).
% 0.20/0.50  fof(f1334,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl6_2 | ~spl6_10 | ~spl6_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1333,f77])).
% 0.20/0.50  fof(f1333,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0) | (spl6_2 | ~spl6_10 | ~spl6_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1332,f78])).
% 0.20/0.50  fof(f1332,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (spl6_2 | ~spl6_10 | ~spl6_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1330,f143])).
% 0.20/0.50  fof(f1330,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (spl6_2 | ~spl6_10 | ~spl6_14)),
% 0.20/0.50    inference(superposition,[],[f1312,f92])).
% 0.20/0.50  fof(f1312,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl6_2 | ~spl6_10 | ~spl6_14)),
% 0.20/0.50    inference(backward_demodulation,[],[f1126,f379])).
% 0.20/0.50  fof(f1126,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl6_2 | ~spl6_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f130,f301])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl6_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f300])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    spl6_10 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl6_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl6_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.50  fof(f506,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_2(X0,k1_xboole_0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f505,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f76,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f505,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X0,k1_xboole_0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f499,f81])).
% 0.20/0.50  fof(f499,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X0,k1_xboole_0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f259,f146])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f73,f81])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f258])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f257,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.20/0.50    inference(superposition,[],[f139,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f123,f119])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f1291,plain,(
% 0.20/0.50    spl6_2 | ~spl6_10 | ~spl6_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1290])).
% 0.20/0.50  fof(f1290,plain,(
% 0.20/0.50    $false | (spl6_2 | ~spl6_10 | ~spl6_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1288,f1280])).
% 0.20/0.50  fof(f1280,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_10 | ~spl6_12)),
% 0.20/0.50    inference(backward_demodulation,[],[f1126,f373])).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl6_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f372])).
% 0.20/0.50  fof(f372,plain,(
% 0.20/0.50    spl6_12 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.50  fof(f1288,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl6_10 | ~spl6_12)),
% 0.20/0.50    inference(backward_demodulation,[],[f1038,f1285])).
% 0.20/0.50  fof(f1285,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | (~spl6_10 | ~spl6_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1281,f1058])).
% 0.20/0.50  fof(f1058,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f1029,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f64])).
% 0.20/0.50  fof(f1029,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl6_10),
% 0.20/0.50    inference(backward_demodulation,[],[f244,f301])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f243,f161])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f105,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f24])).
% 0.20/0.50  fof(f24,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f241,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f89,f240])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    sK1 = k2_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f238,f68])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(superposition,[],[f107,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.50  fof(f1281,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_10 | ~spl6_12)),
% 0.20/0.50    inference(resolution,[],[f1278,f266])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~v1_funct_2(X3,k1_xboole_0,X2) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f265])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f261,f119])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 0.20/0.50    inference(superposition,[],[f140,f106])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f124,f119])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f65])).
% 0.20/0.50  fof(f1278,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_10 | ~spl6_12)),
% 0.20/0.50    inference(backward_demodulation,[],[f1023,f373])).
% 0.20/0.50  fof(f1023,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_10),
% 0.20/0.50    inference(backward_demodulation,[],[f67,f301])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f1038,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | ~spl6_10),
% 0.20/0.50    inference(backward_demodulation,[],[f653,f301])).
% 0.20/0.50  fof(f653,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f652,f161])).
% 0.20/0.50  fof(f652,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f651,f66])).
% 0.20/0.50  fof(f651,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f646,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f646,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f621,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f621,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f620,f161])).
% 0.20/0.50  fof(f620,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f619,f66])).
% 0.20/0.50  fof(f619,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f603,f69])).
% 0.20/0.50  fof(f603,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f219,f240])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f218,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f214,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(superposition,[],[f88,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f1117,plain,(
% 0.20/0.50    spl6_3 | ~spl6_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1116])).
% 0.20/0.50  fof(f1116,plain,(
% 0.20/0.50    $false | (spl6_3 | ~spl6_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1056,f1086])).
% 0.20/0.50  fof(f1086,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl6_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f1085,f72])).
% 0.20/0.50  fof(f1085,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f1084,f301])).
% 0.20/0.50  fof(f1084,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(sK1) | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f989,f301])).
% 0.20/0.50  fof(f989,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(sK1)) | ~v1_xboole_0(sK1)),
% 0.20/0.50    inference(superposition,[],[f720,f157])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f119,f81])).
% 0.20/0.50  fof(f720,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f719,f161])).
% 0.20/0.50  fof(f719,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f718,f66])).
% 0.20/0.50  fof(f718,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f698,f69])).
% 0.20/0.50  % (21676)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  fof(f698,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f217,f240])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f216,f90])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f213,f91])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(superposition,[],[f89,f93])).
% 0.20/0.50  fof(f1056,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl6_3 | ~spl6_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f1026,f119])).
% 0.20/0.50  fof(f1026,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_3 | ~spl6_10)),
% 0.20/0.50    inference(backward_demodulation,[],[f133,f301])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl6_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.50  fof(f1093,plain,(
% 0.20/0.50    spl6_14 | spl6_12 | ~spl6_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f1092,f300,f372,f378])).
% 0.20/0.50  fof(f1092,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl6_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f1091,f72])).
% 0.20/0.50  fof(f1091,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f1090,f301])).
% 0.20/0.50  fof(f1090,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_xboole_0(sK1) | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f1089,f301])).
% 0.20/0.50  fof(f1089,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | sK0 = sK1 | ~v1_xboole_0(sK1) | ~spl6_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f1088,f1058])).
% 0.20/0.50  fof(f1088,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | sK0 = sK1 | ~v1_xboole_0(sK1) | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f1087,f301])).
% 0.20/0.50  fof(f1087,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | sK0 = sK1 | ~v1_xboole_0(sK1) | ~spl6_10),
% 0.20/0.50    inference(forward_demodulation,[],[f766,f301])).
% 0.20/0.50  fof(f766,plain,(
% 0.20/0.50    sK1 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | sK0 = sK1 | ~v1_xboole_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f251,f67])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X2,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X2 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f138,f81])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(forward_demodulation,[],[f122,f118])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f65])).
% 0.20/0.50  fof(f1078,plain,(
% 0.20/0.50    ~spl6_10 | spl6_31),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1077])).
% 0.20/0.50  fof(f1077,plain,(
% 0.20/0.50    $false | (~spl6_10 | spl6_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1076,f72])).
% 0.20/0.50  fof(f1076,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl6_10 | spl6_31)),
% 0.20/0.50    inference(forward_demodulation,[],[f1048,f119])).
% 0.20/0.50  fof(f1048,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2)))) | (~spl6_10 | spl6_31)),
% 0.20/0.50    inference(backward_demodulation,[],[f1004,f301])).
% 0.20/0.50  fof(f1004,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) | spl6_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f1003])).
% 0.20/0.50  fof(f1003,plain,(
% 0.20/0.50    spl6_31 <=> v1_xboole_0(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.50  fof(f1022,plain,(
% 0.20/0.50    spl6_9 | spl6_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f1021,f300,f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    spl6_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.50  fof(f1021,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f333,f67])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f68,f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f65])).
% 0.20/0.50  fof(f1014,plain,(
% 0.20/0.50    spl6_3 | ~spl6_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1013])).
% 0.20/0.50  fof(f1013,plain,(
% 0.20/0.50    $false | (spl6_3 | ~spl6_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1012,f133])).
% 0.20/0.50  fof(f1012,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.20/0.50    inference(forward_demodulation,[],[f1011,f348])).
% 0.20/0.50  fof(f348,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~spl6_9),
% 0.20/0.50    inference(subsumption_resolution,[],[f344,f68])).
% 0.20/0.50  fof(f344,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_9),
% 0.20/0.50    inference(superposition,[],[f298,f106])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f297])).
% 0.20/0.50  fof(f1011,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f1010,f161])).
% 0.20/0.50  fof(f1010,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1009,f66])).
% 0.20/0.50  fof(f1009,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f987,f69])).
% 0.20/0.50  fof(f987,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f720,f94])).
% 0.20/0.50  fof(f1005,plain,(
% 0.20/0.50    spl6_30 | ~spl6_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f985,f1003,f1000])).
% 0.20/0.50  fof(f985,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) | ~r2_hidden(X1,k2_funct_1(sK2))) )),
% 0.20/0.50    inference(resolution,[],[f720,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.50  fof(f656,plain,(
% 0.20/0.50    spl6_2 | ~spl6_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f655])).
% 0.20/0.50  fof(f655,plain,(
% 0.20/0.50    $false | (spl6_2 | ~spl6_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f654,f130])).
% 0.20/0.50  fof(f654,plain,(
% 0.20/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl6_9),
% 0.20/0.50    inference(forward_demodulation,[],[f653,f348])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    spl6_6 | spl6_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f168,f180,f177])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.50    inference(resolution,[],[f115,f76])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    spl6_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    $false | spl6_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f159])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl6_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f158,f66])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl6_1),
% 0.20/0.50    inference(resolution,[],[f91,f127])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl6_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl6_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f71,f132,f129,f126])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (21658)------------------------------
% 0.20/0.50  % (21658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21672)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (21658)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (21658)Memory used [KB]: 11257
% 0.20/0.50  % (21658)Time elapsed: 0.091 s
% 0.20/0.50  % (21658)------------------------------
% 0.20/0.50  % (21658)------------------------------
% 0.20/0.50  % (21655)Success in time 0.15 s
%------------------------------------------------------------------------------
