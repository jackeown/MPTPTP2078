%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:59 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 181 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  266 ( 416 expanded)
%              Number of equality atoms :   60 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f864,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f90,f185,f341,f403,f784,f822,f826,f861])).

fof(f861,plain,
    ( spl3_4
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | spl3_4
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f855,f89])).

fof(f89,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_4
  <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f855,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(superposition,[],[f825,f821])).

fof(f821,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK2),sK1)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl3_46
  <=> sK1 = k9_relat_1(k6_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f825,plain,
    ( ! [X21,X20] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21)) = k9_relat_1(k7_relat_1(sK0,X20),X21)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl3_47
  <=> ! [X20,X21] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21)) = k9_relat_1(k7_relat_1(sK0,X20),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f826,plain,
    ( spl3_47
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f434,f183,f64,f824])).

fof(f64,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f183,plain,
    ( spl3_11
  <=> ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f434,plain,
    ( ! [X21,X20] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21)) = k9_relat_1(k7_relat_1(sK0,X20),X21)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f432,f184])).

fof(f184,plain,
    ( ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f432,plain,
    ( ! [X21,X20] : k9_relat_1(k5_relat_1(k6_relat_1(X20),sK0),X21) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21))
    | ~ spl3_1 ),
    inference(resolution,[],[f177,f66])).

fof(f66,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f177,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f822,plain,
    ( spl3_46
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f812,f781,f819])).

fof(f781,plain,
    ( spl3_44
  <=> r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f812,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK2),sK1)
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f811,f385])).

fof(f385,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) ),
    inference(forward_demodulation,[],[f377,f129])).

fof(f129,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f377,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(resolution,[],[f255,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_relat_1(X0))
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(subsumption_resolution,[],[f160,f41])).

fof(f160,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f151,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f151,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f46,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f255,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f253,f41])).

fof(f253,plain,(
    ! [X2,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f50,f125])).

fof(f125,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f811,plain,
    ( ~ r1_tarski(k9_relat_1(k6_relat_1(sK2),sK1),sK1)
    | sK1 = k9_relat_1(k6_relat_1(sK2),sK1)
    | ~ spl3_44 ),
    inference(resolution,[],[f783,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f783,plain,
    ( r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f781])).

fof(f784,plain,
    ( spl3_44
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f777,f400,f781])).

fof(f400,plain,
    ( spl3_22
  <=> r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f777,plain,
    ( r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f775,f41])).

fof(f775,plain,
    ( r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl3_22 ),
    inference(resolution,[],[f170,f402])).

fof(f402,plain,
    ( r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f400])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f162,f102])).

fof(f102,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f101,f43])).

fof(f101,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f100,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f100,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f44,f41])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f54,f74])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f403,plain,
    ( spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f384,f338,f400])).

fof(f338,plain,
    ( spl3_20
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f384,plain,
    ( r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2))
    | ~ spl3_20 ),
    inference(superposition,[],[f255,f340])).

fof(f340,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f338])).

fof(f341,plain,
    ( spl3_20
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f284,f69,f338])).

fof(f69,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f284,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f138,f71])).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f137,f41])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f185,plain,
    ( spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f124,f64,f183])).

fof(f124,plain,
    ( ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f48,f66])).

fof(f90,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f72,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:28:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (27385)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (27378)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (27373)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (27395)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (27394)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (27387)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (27392)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (27373)Refutation not found, incomplete strategy% (27373)------------------------------
% 0.21/0.51  % (27373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27375)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (27379)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.22/0.52  % (27398)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.22/0.52  % (27391)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.22/0.52  % (27380)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.22/0.52  % (27373)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (27373)Memory used [KB]: 10618
% 1.22/0.52  % (27373)Time elapsed: 0.104 s
% 1.22/0.52  % (27373)------------------------------
% 1.22/0.52  % (27373)------------------------------
% 1.22/0.52  % (27378)Refutation not found, incomplete strategy% (27378)------------------------------
% 1.22/0.52  % (27378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (27374)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.52  % (27377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.22/0.52  % (27378)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  % (27390)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.22/0.52  
% 1.22/0.52  % (27378)Memory used [KB]: 6140
% 1.22/0.52  % (27378)Time elapsed: 0.105 s
% 1.22/0.52  % (27378)------------------------------
% 1.22/0.52  % (27378)------------------------------
% 1.22/0.52  % (27397)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.22/0.52  % (27386)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.22/0.53  % (27384)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.22/0.53  % (27396)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.38/0.53  % (27382)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.53  % (27381)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.54  % (27376)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.38/0.54  % (27388)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.38/0.54  % (27389)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.38/0.55  % (27383)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.38/0.55  % (27393)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.38/0.60  % (27375)Refutation found. Thanks to Tanya!
% 1.38/0.60  % SZS status Theorem for theBenchmark
% 1.38/0.60  % SZS output start Proof for theBenchmark
% 1.38/0.60  fof(f864,plain,(
% 1.38/0.60    $false),
% 1.38/0.60    inference(avatar_sat_refutation,[],[f67,f72,f90,f185,f341,f403,f784,f822,f826,f861])).
% 1.38/0.60  fof(f861,plain,(
% 1.38/0.60    spl3_4 | ~spl3_46 | ~spl3_47),
% 1.38/0.60    inference(avatar_contradiction_clause,[],[f860])).
% 1.38/0.60  fof(f860,plain,(
% 1.38/0.60    $false | (spl3_4 | ~spl3_46 | ~spl3_47)),
% 1.38/0.60    inference(subsumption_resolution,[],[f855,f89])).
% 1.38/0.60  fof(f89,plain,(
% 1.38/0.60    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) | spl3_4),
% 1.38/0.60    inference(avatar_component_clause,[],[f87])).
% 1.38/0.60  fof(f87,plain,(
% 1.38/0.60    spl3_4 <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.38/0.60  fof(f855,plain,(
% 1.38/0.60    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) | (~spl3_46 | ~spl3_47)),
% 1.38/0.60    inference(superposition,[],[f825,f821])).
% 1.38/0.60  fof(f821,plain,(
% 1.38/0.60    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) | ~spl3_46),
% 1.38/0.60    inference(avatar_component_clause,[],[f819])).
% 1.38/0.60  fof(f819,plain,(
% 1.38/0.60    spl3_46 <=> sK1 = k9_relat_1(k6_relat_1(sK2),sK1)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.38/0.60  fof(f825,plain,(
% 1.38/0.60    ( ! [X21,X20] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21)) = k9_relat_1(k7_relat_1(sK0,X20),X21)) ) | ~spl3_47),
% 1.38/0.60    inference(avatar_component_clause,[],[f824])).
% 1.38/0.60  fof(f824,plain,(
% 1.38/0.60    spl3_47 <=> ! [X20,X21] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21)) = k9_relat_1(k7_relat_1(sK0,X20),X21)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.38/0.60  fof(f826,plain,(
% 1.38/0.60    spl3_47 | ~spl3_1 | ~spl3_11),
% 1.38/0.60    inference(avatar_split_clause,[],[f434,f183,f64,f824])).
% 1.38/0.60  fof(f64,plain,(
% 1.38/0.60    spl3_1 <=> v1_relat_1(sK0)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.38/0.60  fof(f183,plain,(
% 1.38/0.60    spl3_11 <=> ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.38/0.60  fof(f434,plain,(
% 1.38/0.60    ( ! [X21,X20] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21)) = k9_relat_1(k7_relat_1(sK0,X20),X21)) ) | (~spl3_1 | ~spl3_11)),
% 1.38/0.60    inference(forward_demodulation,[],[f432,f184])).
% 1.38/0.60  fof(f184,plain,(
% 1.38/0.60    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)) ) | ~spl3_11),
% 1.38/0.60    inference(avatar_component_clause,[],[f183])).
% 1.38/0.60  fof(f432,plain,(
% 1.38/0.60    ( ! [X21,X20] : (k9_relat_1(k5_relat_1(k6_relat_1(X20),sK0),X21) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X20),X21))) ) | ~spl3_1),
% 1.38/0.60    inference(resolution,[],[f177,f66])).
% 1.38/0.60  fof(f66,plain,(
% 1.38/0.60    v1_relat_1(sK0) | ~spl3_1),
% 1.38/0.60    inference(avatar_component_clause,[],[f64])).
% 1.38/0.60  fof(f177,plain,(
% 1.38/0.60    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(k6_relat_1(X3),X2),X4) = k9_relat_1(X2,k9_relat_1(k6_relat_1(X3),X4))) )),
% 1.38/0.60    inference(resolution,[],[f53,f41])).
% 1.38/0.60  fof(f41,plain,(
% 1.38/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f5])).
% 1.38/0.60  fof(f5,axiom,(
% 1.38/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.38/0.60  fof(f53,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f27])).
% 1.38/0.60  fof(f27,plain,(
% 1.38/0.60    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f9])).
% 1.38/0.60  fof(f9,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 1.38/0.60  fof(f822,plain,(
% 1.38/0.60    spl3_46 | ~spl3_44),
% 1.38/0.60    inference(avatar_split_clause,[],[f812,f781,f819])).
% 1.38/0.60  fof(f781,plain,(
% 1.38/0.60    spl3_44 <=> r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.38/0.60  fof(f812,plain,(
% 1.38/0.60    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) | ~spl3_44),
% 1.38/0.60    inference(subsumption_resolution,[],[f811,f385])).
% 1.38/0.60  fof(f385,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)) )),
% 1.38/0.60    inference(forward_demodulation,[],[f377,f129])).
% 1.38/0.60  fof(f129,plain,(
% 1.38/0.60    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.38/0.60    inference(resolution,[],[f49,f41])).
% 1.38/0.60  fof(f49,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f23])).
% 1.38/0.60  fof(f23,plain,(
% 1.38/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f7])).
% 1.38/0.60  fof(f7,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.38/0.60  fof(f377,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 1.38/0.60    inference(resolution,[],[f255,f161])).
% 1.38/0.60  fof(f161,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f160,f41])).
% 1.38/0.60  fof(f160,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.60    inference(superposition,[],[f151,f43])).
% 1.38/0.60  fof(f43,plain,(
% 1.38/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.38/0.60    inference(cnf_transformation,[],[f11])).
% 1.38/0.60  fof(f11,axiom,(
% 1.38/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.38/0.60  fof(f151,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f46,f74])).
% 1.38/0.60  fof(f74,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(X0) | ~r1_tarski(X0,X1)) )),
% 1.38/0.60    inference(resolution,[],[f47,f59])).
% 1.38/0.60  fof(f59,plain,(
% 1.38/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f37])).
% 1.38/0.60  fof(f37,plain,(
% 1.38/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.38/0.60    inference(nnf_transformation,[],[f3])).
% 1.38/0.60  fof(f3,axiom,(
% 1.38/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.60  fof(f47,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f21])).
% 1.38/0.60  fof(f21,plain,(
% 1.38/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f4])).
% 1.38/0.60  fof(f4,axiom,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.60  fof(f46,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f20])).
% 1.38/0.60  fof(f20,plain,(
% 1.38/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(flattening,[],[f19])).
% 1.38/0.60  fof(f19,plain,(
% 1.38/0.60    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f10])).
% 1.38/0.60  fof(f10,axiom,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.38/0.60  fof(f255,plain,(
% 1.38/0.60    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f253,f41])).
% 1.38/0.60  fof(f253,plain,(
% 1.38/0.60    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.38/0.60    inference(superposition,[],[f50,f125])).
% 1.38/0.60  fof(f125,plain,(
% 1.38/0.60    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.38/0.60    inference(resolution,[],[f48,f41])).
% 1.38/0.60  fof(f48,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f22])).
% 1.38/0.60  fof(f22,plain,(
% 1.38/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f13])).
% 1.38/0.60  fof(f13,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.38/0.60  fof(f50,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f24])).
% 1.38/0.60  fof(f24,plain,(
% 1.38/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f12])).
% 1.38/0.60  fof(f12,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.38/0.60  fof(f811,plain,(
% 1.38/0.60    ~r1_tarski(k9_relat_1(k6_relat_1(sK2),sK1),sK1) | sK1 = k9_relat_1(k6_relat_1(sK2),sK1) | ~spl3_44),
% 1.38/0.60    inference(resolution,[],[f783,f57])).
% 1.38/0.60  fof(f57,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.38/0.60    inference(cnf_transformation,[],[f36])).
% 1.38/0.60  fof(f36,plain,(
% 1.38/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.60    inference(flattening,[],[f35])).
% 1.38/0.60  fof(f35,plain,(
% 1.38/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.60    inference(nnf_transformation,[],[f1])).
% 1.38/0.60  fof(f1,axiom,(
% 1.38/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.60  fof(f783,plain,(
% 1.38/0.60    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) | ~spl3_44),
% 1.38/0.60    inference(avatar_component_clause,[],[f781])).
% 1.38/0.60  fof(f784,plain,(
% 1.38/0.60    spl3_44 | ~spl3_22),
% 1.38/0.60    inference(avatar_split_clause,[],[f777,f400,f781])).
% 1.38/0.60  fof(f400,plain,(
% 1.38/0.60    spl3_22 <=> r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.38/0.60  fof(f777,plain,(
% 1.38/0.60    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) | ~spl3_22),
% 1.38/0.60    inference(subsumption_resolution,[],[f775,f41])).
% 1.38/0.60  fof(f775,plain,(
% 1.38/0.60    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) | ~v1_relat_1(k6_relat_1(sK2)) | ~spl3_22),
% 1.38/0.60    inference(resolution,[],[f170,f402])).
% 1.38/0.60  fof(f402,plain,(
% 1.38/0.60    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2)) | ~spl3_22),
% 1.38/0.60    inference(avatar_component_clause,[],[f400])).
% 1.38/0.60  fof(f170,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(superposition,[],[f162,f102])).
% 1.38/0.60  fof(f102,plain,(
% 1.38/0.60    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.38/0.60    inference(forward_demodulation,[],[f101,f43])).
% 1.38/0.60  fof(f101,plain,(
% 1.38/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 1.38/0.60    inference(forward_demodulation,[],[f100,f42])).
% 1.38/0.60  fof(f42,plain,(
% 1.38/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.38/0.60    inference(cnf_transformation,[],[f11])).
% 1.38/0.60  fof(f100,plain,(
% 1.38/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.38/0.60    inference(resolution,[],[f44,f41])).
% 1.38/0.60  fof(f44,plain,(
% 1.38/0.60    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f18])).
% 1.38/0.60  fof(f18,plain,(
% 1.38/0.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f6])).
% 1.38/0.60  fof(f6,axiom,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.38/0.60  fof(f162,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f54,f74])).
% 1.38/0.60  fof(f54,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f29])).
% 1.38/0.60  fof(f29,plain,(
% 1.38/0.60    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(flattening,[],[f28])).
% 1.38/0.60  fof(f28,plain,(
% 1.38/0.60    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f8])).
% 1.38/0.60  fof(f8,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 1.38/0.60  fof(f403,plain,(
% 1.38/0.60    spl3_22 | ~spl3_20),
% 1.38/0.60    inference(avatar_split_clause,[],[f384,f338,f400])).
% 1.38/0.60  fof(f338,plain,(
% 1.38/0.60    spl3_20 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.38/0.60  fof(f384,plain,(
% 1.38/0.60    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2)) | ~spl3_20),
% 1.38/0.60    inference(superposition,[],[f255,f340])).
% 1.38/0.60  fof(f340,plain,(
% 1.38/0.60    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) | ~spl3_20),
% 1.38/0.60    inference(avatar_component_clause,[],[f338])).
% 1.38/0.60  fof(f341,plain,(
% 1.38/0.60    spl3_20 | ~spl3_2),
% 1.38/0.60    inference(avatar_split_clause,[],[f284,f69,f338])).
% 1.38/0.60  fof(f69,plain,(
% 1.38/0.60    spl3_2 <=> r1_tarski(sK1,sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.38/0.60  fof(f284,plain,(
% 1.38/0.60    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) | ~spl3_2),
% 1.38/0.60    inference(resolution,[],[f138,f71])).
% 1.38/0.60  fof(f71,plain,(
% 1.38/0.60    r1_tarski(sK1,sK2) | ~spl3_2),
% 1.38/0.60    inference(avatar_component_clause,[],[f69])).
% 1.38/0.60  fof(f138,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.38/0.60    inference(subsumption_resolution,[],[f137,f41])).
% 1.38/0.60  fof(f137,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.60    inference(superposition,[],[f52,f42])).
% 1.38/0.60  fof(f52,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f26])).
% 1.38/0.60  fof(f26,plain,(
% 1.38/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(flattening,[],[f25])).
% 1.38/0.60  fof(f25,plain,(
% 1.38/0.60    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f14])).
% 1.38/0.60  fof(f14,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.38/0.60  fof(f185,plain,(
% 1.38/0.60    spl3_11 | ~spl3_1),
% 1.38/0.60    inference(avatar_split_clause,[],[f124,f64,f183])).
% 1.38/0.60  fof(f124,plain,(
% 1.38/0.60    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)) ) | ~spl3_1),
% 1.38/0.60    inference(resolution,[],[f48,f66])).
% 1.38/0.60  fof(f90,plain,(
% 1.38/0.60    ~spl3_4),
% 1.38/0.60    inference(avatar_split_clause,[],[f40,f87])).
% 1.38/0.60  fof(f40,plain,(
% 1.38/0.60    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 1.38/0.60    inference(cnf_transformation,[],[f34])).
% 1.38/0.60  fof(f34,plain,(
% 1.38/0.60    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32])).
% 1.38/0.60  fof(f32,plain,(
% 1.38/0.60    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f33,plain,(
% 1.38/0.60    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f17,plain,(
% 1.38/0.60    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f16])).
% 1.38/0.60  fof(f16,negated_conjecture,(
% 1.38/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.38/0.60    inference(negated_conjecture,[],[f15])).
% 1.38/0.60  fof(f15,conjecture,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.38/0.60  fof(f72,plain,(
% 1.38/0.60    spl3_2),
% 1.38/0.60    inference(avatar_split_clause,[],[f39,f69])).
% 1.38/0.60  fof(f39,plain,(
% 1.38/0.60    r1_tarski(sK1,sK2)),
% 1.38/0.60    inference(cnf_transformation,[],[f34])).
% 1.38/0.60  fof(f67,plain,(
% 1.38/0.60    spl3_1),
% 1.38/0.60    inference(avatar_split_clause,[],[f38,f64])).
% 1.38/0.60  fof(f38,plain,(
% 1.38/0.60    v1_relat_1(sK0)),
% 1.38/0.60    inference(cnf_transformation,[],[f34])).
% 1.38/0.60  % SZS output end Proof for theBenchmark
% 1.38/0.60  % (27375)------------------------------
% 1.38/0.60  % (27375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.60  % (27375)Termination reason: Refutation
% 1.38/0.60  
% 1.38/0.60  % (27375)Memory used [KB]: 6908
% 1.38/0.60  % (27375)Time elapsed: 0.186 s
% 1.38/0.60  % (27375)------------------------------
% 1.38/0.60  % (27375)------------------------------
% 1.38/0.60  % (27372)Success in time 0.243 s
%------------------------------------------------------------------------------
