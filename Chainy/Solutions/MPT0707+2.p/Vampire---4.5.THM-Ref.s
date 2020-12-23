%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0707+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 102 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 183 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3476,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1287,f1291,f1652,f3098,f3415,f3468])).

fof(f3468,plain,
    ( spl18_76
    | ~ spl18_84 ),
    inference(avatar_contradiction_clause,[],[f3467])).

fof(f3467,plain,
    ( $false
    | spl18_76
    | ~ spl18_84 ),
    inference(subsumption_resolution,[],[f3466,f3097])).

fof(f3097,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl18_76 ),
    inference(avatar_component_clause,[],[f3096])).

fof(f3096,plain,
    ( spl18_76
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_76])])).

fof(f3466,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl18_84 ),
    inference(forward_demodulation,[],[f3453,f1227])).

fof(f1227,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f3453,plain,
    ( k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl18_84 ),
    inference(superposition,[],[f2882,f3414])).

fof(f3414,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl18_84 ),
    inference(avatar_component_clause,[],[f3413])).

fof(f3413,plain,
    ( spl18_84
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_84])])).

fof(f2882,plain,(
    ! [X33,X32] : k3_xboole_0(X32,X33) = k2_relat_1(k7_relat_1(k6_relat_1(X32),X33)) ),
    inference(superposition,[],[f1227,f2837])).

fof(f2837,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f1221,f1444])).

fof(f1444,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f1219,f1228])).

fof(f1228,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f907])).

fof(f907,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f1219,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f1073])).

fof(f1073,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1221,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f983])).

fof(f983,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f3415,plain,
    ( spl18_84
    | ~ spl18_13 ),
    inference(avatar_split_clause,[],[f3400,f1351,f3413])).

fof(f1351,plain,
    ( spl18_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).

fof(f3400,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl18_13 ),
    inference(resolution,[],[f3260,f1352])).

fof(f1352,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl18_13 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f3260,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f1536,f2837])).

fof(f1536,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X1,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f1535,f1221])).

fof(f1535,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f1532,f1227])).

fof(f1532,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f1216,f1228])).

fof(f1216,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f1071])).

fof(f1071,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1070])).

fof(f1070,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f871])).

fof(f871,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f3098,plain,
    ( ~ spl18_76
    | spl18_1 ),
    inference(avatar_split_clause,[],[f3078,f1285,f3096])).

fof(f1285,plain,
    ( spl18_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f3078,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl18_1 ),
    inference(superposition,[],[f1286,f3050])).

fof(f3050,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f1439,f2882])).

fof(f1439,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f1175,f1228])).

fof(f1175,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f1041])).

fof(f1041,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1286,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl18_1 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1652,plain,
    ( spl18_13
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1648,f1289,f1351])).

fof(f1289,plain,
    ( spl18_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f1648,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl18_2 ),
    inference(resolution,[],[f1290,f1238])).

fof(f1238,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1135])).

fof(f1135,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1290,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f1289])).

fof(f1291,plain,(
    spl18_2 ),
    inference(avatar_split_clause,[],[f1156,f1289])).

fof(f1156,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f1103])).

fof(f1103,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1022,f1102])).

fof(f1102,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1022,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f966])).

fof(f966,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f965])).

fof(f965,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f1287,plain,(
    ~ spl18_1 ),
    inference(avatar_split_clause,[],[f1157,f1285])).

fof(f1157,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f1103])).
%------------------------------------------------------------------------------
