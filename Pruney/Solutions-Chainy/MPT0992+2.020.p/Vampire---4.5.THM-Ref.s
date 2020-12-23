%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 838 expanded)
%              Number of leaves         :   28 ( 216 expanded)
%              Depth                    :   17
%              Number of atoms          :  491 (5135 expanded)
%              Number of equality atoms :   88 (1092 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f111,f158,f344,f346,f713,f721,f817,f966,f1002,f1008,f1009,f1071,f1118])).

fof(f1118,plain,
    ( ~ spl4_9
    | ~ spl4_26
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f1117])).

fof(f1117,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_26
    | spl4_37 ),
    inference(subsumption_resolution,[],[f1079,f1100])).

fof(f1100,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0))
    | ~ spl4_9
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f351,f1016])).

fof(f1016,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_9 ),
    inference(resolution,[],[f136,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f136,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f351,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl4_26
  <=> ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1079,plain,
    ( ~ v1_xboole_0(k7_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_9
    | spl4_37 ),
    inference(forward_demodulation,[],[f832,f1016])).

fof(f832,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f831])).

fof(f831,plain,
    ( spl4_37
  <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1071,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f1070])).

fof(f1070,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f1067,f1054])).

fof(f1054,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f1053,f850])).

fof(f850,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_37 ),
    inference(resolution,[],[f833,f58])).

fof(f833,plain,
    ( v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f831])).

fof(f1053,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1052,f1045])).

fof(f1045,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f1044,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1044,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f339,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f339,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f52,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f1052,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f169,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f169,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f97,f140])).

fof(f140,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    ! [X0] :
      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1067,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f1046,f1016])).

fof(f1046,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f1017,f110])).

fof(f1017,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f50,f105])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f1009,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f549,f134,f130])).

fof(f130,plain,
    ( spl4_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f549,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f51,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f1008,plain,
    ( ~ spl4_8
    | spl4_26 ),
    inference(avatar_split_clause,[],[f583,f350,f130])).

fof(f583,plain,(
    ! [X0] :
      ( v1_xboole_0(k7_relat_1(sK3,X0))
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f172,f59])).

fof(f172,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f171,f49])).

fof(f171,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f170,f51])).

fof(f170,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f82,f140])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1002,plain,
    ( spl4_25
    | spl4_4 ),
    inference(avatar_split_clause,[],[f556,f104,f318])).

fof(f318,plain,
    ( spl4_25
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f556,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f553,f50])).

fof(f553,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f966,plain,
    ( spl4_3
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f965])).

fof(f965,plain,
    ( $false
    | spl4_3
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f956,f200])).

fof(f200,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f199,f177])).

fof(f177,plain,(
    ! [X1] : v1_relat_1(k7_relat_1(sK3,X1)) ),
    inference(resolution,[],[f172,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f199,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f179,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f179,plain,(
    ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1) ),
    inference(resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f956,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_25 ),
    inference(resolution,[],[f734,f818])).

fof(f818,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f101,f140])).

fof(f101,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f734,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f733,f177])).

fof(f733,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f724,f168])).

fof(f168,plain,(
    ! [X1] : v1_funct_1(k7_relat_1(sK3,X1)) ),
    inference(backward_demodulation,[],[f141,f140])).

fof(f141,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X1] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f724,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_25 ),
    inference(superposition,[],[f67,f719])).

fof(f719,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_25 ),
    inference(resolution,[],[f52,f577])).

fof(f577,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f572,f123])).

fof(f123,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f71])).

fof(f572,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl4_25 ),
    inference(superposition,[],[f62,f569])).

fof(f569,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f124,f320])).

fof(f320,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f318])).

fof(f124,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f817,plain,
    ( spl4_2
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f816])).

fof(f816,plain,
    ( $false
    | spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f815,f169])).

fof(f815,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_25 ),
    inference(resolution,[],[f732,f200])).

fof(f732,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f731,f177])).

fof(f731,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f723,f168])).

fof(f723,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ v1_funct_1(k7_relat_1(sK3,sK2))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_25 ),
    inference(superposition,[],[f66,f719])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f721,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f720,f118,f114])).

fof(f114,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f118,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f720,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f52,f70])).

fof(f713,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f711,f172])).

fof(f711,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f710,f140])).

fof(f710,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f101,f120])).

fof(f120,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f346,plain,
    ( ~ spl4_5
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl4_5
    | spl4_8 ),
    inference(subsumption_resolution,[],[f341,f55])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f341,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | spl4_8 ),
    inference(backward_demodulation,[],[f132,f110])).

fof(f132,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f344,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f340,f56])).

fof(f340,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f116,f110])).

fof(f116,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f158,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f141,f93])).

fof(f93,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f111,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f53,f108,f104])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f99,f95,f91])).

fof(f54,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:49:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (16821)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.45  % (16821)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f1119,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f102,f111,f158,f344,f346,f713,f721,f817,f966,f1002,f1008,f1009,f1071,f1118])).
% 0.21/0.45  fof(f1118,plain,(
% 0.21/0.45    ~spl4_9 | ~spl4_26 | spl4_37),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1117])).
% 0.21/0.45  fof(f1117,plain,(
% 0.21/0.45    $false | (~spl4_9 | ~spl4_26 | spl4_37)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1079,f1100])).
% 0.21/0.45  fof(f1100,plain,(
% 0.21/0.45    ( ! [X0] : (v1_xboole_0(k7_relat_1(k1_xboole_0,X0))) ) | (~spl4_9 | ~spl4_26)),
% 0.21/0.45    inference(forward_demodulation,[],[f351,f1016])).
% 0.21/0.45  fof(f1016,plain,(
% 0.21/0.45    k1_xboole_0 = sK3 | ~spl4_9),
% 0.21/0.45    inference(resolution,[],[f136,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    v1_xboole_0(sK3) | ~spl4_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f134])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    spl4_9 <=> v1_xboole_0(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.45  fof(f351,plain,(
% 0.21/0.45    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK3,X0))) ) | ~spl4_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f350])).
% 0.21/0.45  fof(f350,plain,(
% 0.21/0.45    spl4_26 <=> ! [X0] : v1_xboole_0(k7_relat_1(sK3,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.45  fof(f1079,plain,(
% 0.21/0.45    ~v1_xboole_0(k7_relat_1(k1_xboole_0,k1_xboole_0)) | (~spl4_9 | spl4_37)),
% 0.21/0.45    inference(forward_demodulation,[],[f832,f1016])).
% 0.21/0.45  fof(f832,plain,(
% 0.21/0.45    ~v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) | spl4_37),
% 0.21/0.45    inference(avatar_component_clause,[],[f831])).
% 0.21/0.45  fof(f831,plain,(
% 0.21/0.45    spl4_37 <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.45  fof(f1071,plain,(
% 0.21/0.45    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_37),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1070])).
% 0.21/0.45  fof(f1070,plain,(
% 0.21/0.45    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_37)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1067,f1054])).
% 0.21/0.45  fof(f1054,plain,(
% 0.21/0.45    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_37)),
% 0.21/0.45    inference(forward_demodulation,[],[f1053,f850])).
% 0.21/0.45  fof(f850,plain,(
% 0.21/0.45    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_37),
% 0.21/0.45    inference(resolution,[],[f833,f58])).
% 0.21/0.45  fof(f833,plain,(
% 0.21/0.45    v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) | ~spl4_37),
% 0.21/0.45    inference(avatar_component_clause,[],[f831])).
% 0.21/0.45  fof(f1053,plain,(
% 0.21/0.45    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.45    inference(forward_demodulation,[],[f1052,f1045])).
% 0.21/0.45  fof(f1045,plain,(
% 0.21/0.45    k1_xboole_0 = sK2 | ~spl4_5),
% 0.21/0.45    inference(subsumption_resolution,[],[f1044,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.45  fof(f1044,plain,(
% 0.21/0.45    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl4_5),
% 0.21/0.45    inference(resolution,[],[f339,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.45    inference(flattening,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.45  fof(f339,plain,(
% 0.21/0.45    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 0.21/0.45    inference(backward_demodulation,[],[f52,f110])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    r1_tarski(sK2,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.45    inference(flattening,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.45    inference(ennf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f19])).
% 0.21/0.45  fof(f19,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.45  fof(f1052,plain,(
% 0.21/0.45    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.21/0.45    inference(forward_demodulation,[],[f169,f105])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f104])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.45    inference(backward_demodulation,[],[f97,f140])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f127,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    v1_funct_1(sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) | ~v1_funct_1(sK3)) )),
% 0.21/0.45    inference(resolution,[],[f51,f80])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.45    inference(flattening,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f1067,plain,(
% 0.21/0.45    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_9)),
% 0.21/0.45    inference(backward_demodulation,[],[f1046,f1016])).
% 0.21/0.45  fof(f1046,plain,(
% 0.21/0.45    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.21/0.45    inference(forward_demodulation,[],[f1017,f110])).
% 0.21/0.45  fof(f1017,plain,(
% 0.21/0.45    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 0.21/0.45    inference(backward_demodulation,[],[f50,f105])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f1009,plain,(
% 0.21/0.45    ~spl4_8 | spl4_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f549,f134,f130])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    spl4_8 <=> v1_xboole_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.45  fof(f549,plain,(
% 0.21/0.45    v1_xboole_0(sK3) | ~v1_xboole_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f51,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.45  fof(f1008,plain,(
% 0.21/0.45    ~spl4_8 | spl4_26),
% 0.21/0.45    inference(avatar_split_clause,[],[f583,f350,f130])).
% 0.21/0.45  fof(f583,plain,(
% 0.21/0.45    ( ! [X0] : (v1_xboole_0(k7_relat_1(sK3,X0)) | ~v1_xboole_0(sK0)) )),
% 0.21/0.45    inference(resolution,[],[f172,f59])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f171,f49])).
% 0.21/0.45  fof(f171,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f170,f51])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.45    inference(superposition,[],[f82,f140])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.45    inference(flattening,[],[f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.45  fof(f1002,plain,(
% 0.21/0.45    spl4_25 | spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f556,f104,f318])).
% 0.21/0.45  fof(f318,plain,(
% 0.21/0.45    spl4_25 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.45  fof(f556,plain,(
% 0.21/0.45    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f553,f50])).
% 0.21/0.45  fof(f553,plain,(
% 0.21/0.45    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(resolution,[],[f51,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.45  fof(f966,plain,(
% 0.21/0.45    spl4_3 | ~spl4_25),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f965])).
% 0.21/0.45  fof(f965,plain,(
% 0.21/0.45    $false | (spl4_3 | ~spl4_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f956,f200])).
% 0.21/0.45  fof(f200,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f199,f177])).
% 0.21/0.45  fof(f177,plain,(
% 0.21/0.45    ( ! [X1] : (v1_relat_1(k7_relat_1(sK3,X1))) )),
% 0.21/0.45    inference(resolution,[],[f172,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.21/0.45    inference(resolution,[],[f179,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    ( ! [X3] : (v5_relat_1(k7_relat_1(sK3,X3),sK1)) )),
% 0.21/0.45    inference(resolution,[],[f172,f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.45    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.45  fof(f956,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_25)),
% 0.21/0.45    inference(resolution,[],[f734,f818])).
% 0.21/0.45  fof(f818,plain,(
% 0.21/0.45    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.45    inference(forward_demodulation,[],[f101,f140])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f99])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f734,plain,(
% 0.21/0.45    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)) ) | ~spl4_25),
% 0.21/0.45    inference(subsumption_resolution,[],[f733,f177])).
% 0.21/0.45  fof(f733,plain,(
% 0.21/0.45    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_25),
% 0.21/0.45    inference(subsumption_resolution,[],[f724,f168])).
% 0.21/0.45  fof(f168,plain,(
% 0.21/0.45    ( ! [X1] : (v1_funct_1(k7_relat_1(sK3,X1))) )),
% 0.21/0.45    inference(backward_demodulation,[],[f141,f140])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f128,f49])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) | ~v1_funct_1(sK3)) )),
% 0.21/0.45    inference(resolution,[],[f51,f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f42])).
% 0.21/0.45  fof(f724,plain,(
% 0.21/0.45    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_25),
% 0.21/0.45    inference(superposition,[],[f67,f719])).
% 0.21/0.45  fof(f719,plain,(
% 0.21/0.45    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_25),
% 0.21/0.45    inference(resolution,[],[f52,f577])).
% 0.21/0.45  fof(f577,plain,(
% 0.21/0.45    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | ~spl4_25),
% 0.21/0.45    inference(subsumption_resolution,[],[f572,f123])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    v1_relat_1(sK3)),
% 0.21/0.45    inference(resolution,[],[f51,f71])).
% 0.21/0.45  fof(f572,plain,(
% 0.21/0.45    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl4_25),
% 0.21/0.45    inference(superposition,[],[f62,f569])).
% 0.21/0.45  fof(f569,plain,(
% 0.21/0.45    sK0 = k1_relat_1(sK3) | ~spl4_25),
% 0.21/0.45    inference(forward_demodulation,[],[f124,f320])).
% 0.21/0.45  fof(f320,plain,(
% 0.21/0.45    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f318])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.45    inference(resolution,[],[f51,f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.45  fof(f817,plain,(
% 0.21/0.45    spl4_2 | ~spl4_25),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f816])).
% 0.21/0.45  fof(f816,plain,(
% 0.21/0.45    $false | (spl4_2 | ~spl4_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f815,f169])).
% 0.21/0.45  fof(f815,plain,(
% 0.21/0.45    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_25),
% 0.21/0.45    inference(resolution,[],[f732,f200])).
% 0.21/0.45  fof(f732,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | ~spl4_25),
% 0.21/0.45    inference(subsumption_resolution,[],[f731,f177])).
% 0.21/0.45  fof(f731,plain,(
% 0.21/0.45    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_25),
% 0.21/0.45    inference(subsumption_resolution,[],[f723,f168])).
% 0.21/0.45  fof(f723,plain,(
% 0.21/0.45    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_25),
% 0.21/0.45    inference(superposition,[],[f66,f719])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f721,plain,(
% 0.21/0.45    ~spl4_6 | spl4_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f720,f118,f114])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    spl4_6 <=> r1_tarski(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    spl4_7 <=> sK0 = sK2),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.45  fof(f720,plain,(
% 0.21/0.45    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.21/0.45    inference(resolution,[],[f52,f70])).
% 0.21/0.45  fof(f713,plain,(
% 0.21/0.45    spl4_3 | ~spl4_7),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f712])).
% 0.21/0.45  fof(f712,plain,(
% 0.21/0.45    $false | (spl4_3 | ~spl4_7)),
% 0.21/0.45    inference(subsumption_resolution,[],[f711,f172])).
% 0.21/0.45  fof(f711,plain,(
% 0.21/0.45    ~m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f710,f140])).
% 0.21/0.45  fof(f710,plain,(
% 0.21/0.45    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f101,f120])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    sK0 = sK2 | ~spl4_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f118])).
% 0.21/0.45  fof(f346,plain,(
% 0.21/0.45    ~spl4_5 | spl4_8),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f345])).
% 0.21/0.45  fof(f345,plain,(
% 0.21/0.45    $false | (~spl4_5 | spl4_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f341,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.45  fof(f341,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | spl4_8)),
% 0.21/0.45    inference(backward_demodulation,[],[f132,f110])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ~v1_xboole_0(sK0) | spl4_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f130])).
% 0.21/0.45  fof(f344,plain,(
% 0.21/0.45    ~spl4_5 | spl4_6),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f343])).
% 0.21/0.45  fof(f343,plain,(
% 0.21/0.45    $false | (~spl4_5 | spl4_6)),
% 0.21/0.45    inference(subsumption_resolution,[],[f340,f56])).
% 0.21/0.45  fof(f340,plain,(
% 0.21/0.45    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 0.21/0.45    inference(backward_demodulation,[],[f116,f110])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ~r1_tarski(sK0,sK2) | spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f114])).
% 0.21/0.45  fof(f158,plain,(
% 0.21/0.45    spl4_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    $false | spl4_1),
% 0.21/0.45    inference(resolution,[],[f141,f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ~spl4_4 | spl4_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f53,f108,f104])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f54,f99,f95,f91])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f44])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (16821)------------------------------
% 0.21/0.45  % (16821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16821)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (16821)Memory used [KB]: 11001
% 0.21/0.45  % (16821)Time elapsed: 0.029 s
% 0.21/0.45  % (16821)------------------------------
% 0.21/0.45  % (16821)------------------------------
% 0.21/0.46  % (16819)Success in time 0.09 s
%------------------------------------------------------------------------------
