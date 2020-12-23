%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 416 expanded)
%              Number of leaves         :   50 ( 173 expanded)
%              Depth                    :   13
%              Number of atoms          :  688 (1271 expanded)
%              Number of equality atoms :  116 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1000,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f112,f117,f122,f135,f148,f171,f176,f223,f234,f255,f273,f281,f296,f305,f318,f372,f374,f402,f488,f535,f569,f609,f610,f628,f699,f745,f746,f754,f796,f981,f998,f999])).

fof(f999,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f998,plain,
    ( spl3_10
    | ~ spl3_69 ),
    inference(avatar_contradiction_clause,[],[f997])).

fof(f997,plain,
    ( $false
    | spl3_10
    | ~ spl3_69 ),
    inference(subsumption_resolution,[],[f996,f155])).

fof(f155,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_10
  <=> v1_xboole_0(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f996,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_69 ),
    inference(subsumption_resolution,[],[f989,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f989,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_69 ),
    inference(resolution,[],[f980,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f980,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl3_69
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f981,plain,
    ( spl3_69
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f801,f302,f270,f252,f168,f145,f978])).

fof(f145,plain,
    ( spl3_9
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f168,plain,
    ( spl3_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f252,plain,
    ( spl3_22
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f270,plain,
    ( spl3_23
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

% (20357)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f302,plain,
    ( spl3_27
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f801,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f493,f304])).

fof(f304,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f302])).

fof(f493,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f484,f254])).

fof(f254,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f252])).

fof(f484,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f188,f272])).

fof(f272,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f188,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f182,f170])).

fof(f170,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f182,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_9 ),
    inference(resolution,[],[f146,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f146,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f796,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_51
    | spl3_59 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_51
    | spl3_59 ),
    inference(resolution,[],[f783,f753])).

fof(f753,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f751])).

fof(f751,plain,
    ( spl3_59
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f783,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f782,f52])).

fof(f52,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f782,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f781,f627])).

fof(f627,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl3_51
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f781,plain,
    ( ! [X1] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f780,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f780,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f779,f304])).

fof(f779,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f778,f233])).

fof(f233,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl3_19
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f778,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X1)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) )
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f97,f134])).

fof(f134,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f97,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f89,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f89,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f754,plain,
    ( ~ spl3_59
    | spl3_41
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f747,f532,f506,f751])).

fof(f506,plain,
    ( spl3_41
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f532,plain,
    ( spl3_42
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f747,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_41
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f507,f534])).

fof(f534,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f532])).

fof(f507,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_41 ),
    inference(avatar_component_clause,[],[f506])).

fof(f746,plain,
    ( spl3_58
    | spl3_36
    | ~ spl3_41
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f740,f696,f532,f506,f399,f742])).

fof(f742,plain,
    ( spl3_58
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f399,plain,
    ( spl3_36
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f696,plain,
    ( spl3_55
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f740,plain,
    ( k1_xboole_0 = sK0
    | spl3_36
    | ~ spl3_41
    | ~ spl3_42
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f739,f698])).

fof(f698,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f696])).

fof(f739,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | spl3_36
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f521,f534])).

fof(f521,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_36
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f514,f401])).

fof(f401,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f399])).

fof(f514,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ spl3_41 ),
    inference(resolution,[],[f508,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f508,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f506])).

fof(f745,plain,
    ( ~ spl3_58
    | spl3_29
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f561,f532,f311,f742])).

fof(f311,plain,
    ( spl3_29
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f561,plain,
    ( k1_xboole_0 != sK0
    | spl3_29
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f554,f53])).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f554,plain,
    ( k2_relat_1(k1_xboole_0) != sK0
    | spl3_29
    | ~ spl3_42 ),
    inference(superposition,[],[f312,f534])).

fof(f312,plain,
    ( sK0 != k2_relat_1(k2_funct_1(sK2))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f311])).

fof(f699,plain,
    ( spl3_55
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f623,f532,f506,f302,f252,f696])).

fof(f623,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f523,f534])).

fof(f523,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f522,f304])).

fof(f522,plain,
    ( sK1 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f516,f254])).

fof(f516,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ spl3_41 ),
    inference(resolution,[],[f508,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f628,plain,
    ( spl3_51
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f619,f158,f625])).

fof(f158,plain,
    ( spl3_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f619,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(resolution,[],[f160,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f160,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f610,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 != k2_funct_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f609,plain,
    ( spl3_48
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f570,f541,f606])).

fof(f606,plain,
    ( spl3_48
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f541,plain,
    ( spl3_44
  <=> k2_relat_1(k1_xboole_0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f570,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f543,f53])).

fof(f543,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(sK2)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f541])).

fof(f569,plain,
    ( k1_xboole_0 != k2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k1_xboole_0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f535,plain,
    ( spl3_42
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f528,f153,f532])).

fof(f528,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_10 ),
    inference(resolution,[],[f154,f57])).

fof(f154,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f153])).

% (20353)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f488,plain,
    ( spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f486,f139])).

fof(f139,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_7
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f486,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f485,f254])).

fof(f485,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f484,f309])).

fof(f309,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl3_28
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f402,plain,
    ( ~ spl3_36
    | spl3_8
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f384,f302,f141,f399])).

fof(f141,plain,
    ( spl3_8
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f384,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_8
    | ~ spl3_27 ),
    inference(superposition,[],[f143,f304])).

fof(f143,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f374,plain,
    ( sK0 != k2_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f372,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f370,f143])).

fof(f370,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f317,f309])).

fof(f317,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f316,f254])).

fof(f316,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f187,f272])).

fof(f187,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f181,f170])).

fof(f181,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9 ),
    inference(resolution,[],[f146,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f318,plain,
    ( spl3_28
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f314,f298,f220,f307])).

fof(f220,plain,
    ( spl3_17
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

% (20355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f298,plain,
    ( spl3_26
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f314,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(superposition,[],[f300,f222])).

fof(f222,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f220])).

fof(f300,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f298])).

fof(f305,plain,
    ( spl3_26
    | spl3_27
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f130,f114,f109,f302,f298])).

fof(f109,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f114,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f124,f111])).

fof(f111,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f116,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f296,plain,
    ( ~ spl3_25
    | spl3_11
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f291,f278,f158,f293])).

fof(f293,plain,
    ( spl3_25
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f278,plain,
    ( spl3_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f291,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl3_11
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f287,f159])).

fof(f159,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f287,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f280,f66])).

fof(f280,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f281,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f275,f231,f132,f87,f278])).

fof(f275,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f274,f233])).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f101,f134])).

fof(f101,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1 ),
    inference(resolution,[],[f89,f61])).

fof(f273,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f256,f132,f92,f87,f270])).

fof(f92,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f256,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f107,f134])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f104,f89])).

fof(f104,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f94,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f255,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f250,f231,f132,f92,f87,f252])).

fof(f250,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f249,f233])).

fof(f249,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f106,f134])).

fof(f106,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f103,f89])).

fof(f103,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f234,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f229,f119,f114,f231])).

fof(f119,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f229,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f126,f121])).

fof(f121,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f126,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f116,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f223,plain,
    ( spl3_17
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f125,f114,f220])).

fof(f125,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f116,f74])).

fof(f176,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | spl3_9 ),
    inference(subsumption_resolution,[],[f174,f147])).

fof(f147,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f174,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f99,f134])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f89,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f171,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f166,f132,f87,f168])).

fof(f166,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f98,f134])).

fof(f98,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f89,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f148,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f45,f145,f141,f137])).

fof(f45,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f135,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f127,f114,f132])).

fof(f127,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f122,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f119])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f117,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f114])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f92])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:40:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (20351)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (20359)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (20347)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (20346)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (20349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (20352)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (20348)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (20358)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (20362)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (20343)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20350)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (20344)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (20356)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (20344)Refutation not found, incomplete strategy% (20344)------------------------------
% 0.22/0.51  % (20344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20344)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20344)Memory used [KB]: 10618
% 0.22/0.51  % (20344)Time elapsed: 0.092 s
% 0.22/0.51  % (20344)------------------------------
% 0.22/0.51  % (20344)------------------------------
% 0.22/0.51  % (20354)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (20346)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f1000,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f90,f95,f112,f117,f122,f135,f148,f171,f176,f223,f234,f255,f273,f281,f296,f305,f318,f372,f374,f402,f488,f535,f569,f609,f610,f628,f699,f745,f746,f754,f796,f981,f998,f999])).
% 0.22/0.51  fof(f999,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f998,plain,(
% 0.22/0.51    spl3_10 | ~spl3_69),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f997])).
% 0.22/0.51  fof(f997,plain,(
% 0.22/0.51    $false | (spl3_10 | ~spl3_69)),
% 0.22/0.51    inference(subsumption_resolution,[],[f996,f155])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_funct_1(sK2)) | spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f153])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    spl3_10 <=> v1_xboole_0(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f996,plain,(
% 0.22/0.51    v1_xboole_0(k2_funct_1(sK2)) | ~spl3_69),
% 0.22/0.51    inference(subsumption_resolution,[],[f989,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f989,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_funct_1(sK2)) | ~spl3_69),
% 0.22/0.51    inference(resolution,[],[f980,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.22/0.51  fof(f980,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | ~spl3_69),
% 0.22/0.51    inference(avatar_component_clause,[],[f978])).
% 0.22/0.51  fof(f978,plain,(
% 0.22/0.51    spl3_69 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.22/0.51  fof(f981,plain,(
% 0.22/0.51    spl3_69 | ~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f801,f302,f270,f252,f168,f145,f978])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl3_9 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    spl3_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    spl3_22 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl3_23 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.51  % (20357)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    spl3_27 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.51  fof(f801,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_27)),
% 0.22/0.51    inference(forward_demodulation,[],[f493,f304])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl3_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f302])).
% 0.22/0.51  fof(f493,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23)),
% 0.22/0.51    inference(forward_demodulation,[],[f484,f254])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f252])).
% 0.22/0.51  fof(f484,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_9 | ~spl3_13 | ~spl3_23)),
% 0.22/0.51    inference(forward_demodulation,[],[f188,f272])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f270])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_9 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f182,f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl3_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f168])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f146,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f145])).
% 0.22/0.51  fof(f796,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_6 | ~spl3_19 | ~spl3_27 | ~spl3_51 | spl3_59),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f784])).
% 0.22/0.51  fof(f784,plain,(
% 0.22/0.51    $false | (~spl3_1 | ~spl3_6 | ~spl3_19 | ~spl3_27 | ~spl3_51 | spl3_59)),
% 0.22/0.51    inference(resolution,[],[f783,f753])).
% 0.22/0.51  fof(f753,plain,(
% 0.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_59),
% 0.22/0.51    inference(avatar_component_clause,[],[f751])).
% 0.22/0.51  fof(f751,plain,(
% 0.22/0.51    spl3_59 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.22/0.51  fof(f783,plain,(
% 0.22/0.51    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_1 | ~spl3_6 | ~spl3_19 | ~spl3_27 | ~spl3_51)),
% 0.22/0.51    inference(forward_demodulation,[],[f782,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.51  fof(f782,plain,(
% 0.22/0.51    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1)))) ) | (~spl3_1 | ~spl3_6 | ~spl3_19 | ~spl3_27 | ~spl3_51)),
% 0.22/0.51    inference(forward_demodulation,[],[f781,f627])).
% 0.22/0.51  fof(f627,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl3_51),
% 0.22/0.51    inference(avatar_component_clause,[],[f625])).
% 0.22/0.51  fof(f625,plain,(
% 0.22/0.51    spl3_51 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.51  fof(f781,plain,(
% 0.22/0.51    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))) ) | (~spl3_1 | ~spl3_6 | ~spl3_19 | ~spl3_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f780,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f780,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))) ) | (~spl3_1 | ~spl3_6 | ~spl3_19 | ~spl3_27)),
% 0.22/0.51    inference(forward_demodulation,[],[f779,f304])).
% 0.22/0.51  fof(f779,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(sK1,X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))) ) | (~spl3_1 | ~spl3_6 | ~spl3_19)),
% 0.22/0.51    inference(forward_demodulation,[],[f778,f233])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | ~spl3_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f231])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    spl3_19 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.51  fof(f778,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(k2_relat_1(sK2),X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))) ) | (~spl3_1 | ~spl3_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f134])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl3_6 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X1] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X1)))) ) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f89,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f754,plain,(
% 0.22/0.51    ~spl3_59 | spl3_41 | ~spl3_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f747,f532,f506,f751])).
% 0.22/0.51  fof(f506,plain,(
% 0.22/0.51    spl3_41 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.51  fof(f532,plain,(
% 0.22/0.51    spl3_42 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.22/0.51  fof(f747,plain,(
% 0.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_41 | ~spl3_42)),
% 0.22/0.51    inference(forward_demodulation,[],[f507,f534])).
% 0.22/0.51  fof(f534,plain,(
% 0.22/0.51    k1_xboole_0 = k2_funct_1(sK2) | ~spl3_42),
% 0.22/0.51    inference(avatar_component_clause,[],[f532])).
% 0.22/0.51  fof(f507,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f506])).
% 0.22/0.51  fof(f746,plain,(
% 0.22/0.51    spl3_58 | spl3_36 | ~spl3_41 | ~spl3_42 | ~spl3_55),
% 0.22/0.51    inference(avatar_split_clause,[],[f740,f696,f532,f506,f399,f742])).
% 0.22/0.51  fof(f742,plain,(
% 0.22/0.51    spl3_58 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    spl3_36 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.51  fof(f696,plain,(
% 0.22/0.51    spl3_55 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.51  fof(f740,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (spl3_36 | ~spl3_41 | ~spl3_42 | ~spl3_55)),
% 0.22/0.51    inference(subsumption_resolution,[],[f739,f698])).
% 0.22/0.51  fof(f698,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | ~spl3_55),
% 0.22/0.51    inference(avatar_component_clause,[],[f696])).
% 0.22/0.51  fof(f739,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | (spl3_36 | ~spl3_41 | ~spl3_42)),
% 0.22/0.51    inference(forward_demodulation,[],[f521,f534])).
% 0.22/0.51  fof(f521,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl3_36 | ~spl3_41)),
% 0.22/0.51    inference(subsumption_resolution,[],[f514,f401])).
% 0.22/0.51  fof(f401,plain,(
% 0.22/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | spl3_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f399])).
% 0.22/0.51  fof(f514,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~spl3_41),
% 0.22/0.51    inference(resolution,[],[f508,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f508,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f506])).
% 0.22/0.51  fof(f745,plain,(
% 0.22/0.51    ~spl3_58 | spl3_29 | ~spl3_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f561,f532,f311,f742])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    spl3_29 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.51  fof(f561,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | (spl3_29 | ~spl3_42)),
% 0.22/0.51    inference(forward_demodulation,[],[f554,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f554,plain,(
% 0.22/0.51    k2_relat_1(k1_xboole_0) != sK0 | (spl3_29 | ~spl3_42)),
% 0.22/0.51    inference(superposition,[],[f312,f534])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    sK0 != k2_relat_1(k2_funct_1(sK2)) | spl3_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f311])).
% 0.22/0.51  fof(f699,plain,(
% 0.22/0.51    spl3_55 | ~spl3_22 | ~spl3_27 | ~spl3_41 | ~spl3_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f623,f532,f506,f302,f252,f696])).
% 0.22/0.51  fof(f623,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_22 | ~spl3_27 | ~spl3_41 | ~spl3_42)),
% 0.22/0.51    inference(forward_demodulation,[],[f523,f534])).
% 0.22/0.51  fof(f523,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (~spl3_22 | ~spl3_27 | ~spl3_41)),
% 0.22/0.51    inference(forward_demodulation,[],[f522,f304])).
% 0.22/0.51  fof(f522,plain,(
% 0.22/0.51    sK1 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (~spl3_22 | ~spl3_41)),
% 0.22/0.51    inference(forward_demodulation,[],[f516,f254])).
% 0.22/0.51  fof(f516,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | ~spl3_41),
% 0.22/0.51    inference(resolution,[],[f508,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f628,plain,(
% 0.22/0.51    spl3_51 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f619,f158,f625])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    spl3_11 <=> v1_xboole_0(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f619,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl3_11),
% 0.22/0.51    inference(resolution,[],[f160,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    v1_xboole_0(sK2) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f158])).
% 0.22/0.51  fof(f610,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 != k2_funct_1(sK2) | v1_xboole_0(k1_relat_1(sK2)) | ~v1_xboole_0(k2_funct_1(sK2))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f609,plain,(
% 0.22/0.51    spl3_48 | ~spl3_44),
% 0.22/0.51    inference(avatar_split_clause,[],[f570,f541,f606])).
% 0.22/0.51  fof(f606,plain,(
% 0.22/0.51    spl3_48 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.51  fof(f541,plain,(
% 0.22/0.51    spl3_44 <=> k2_relat_1(k1_xboole_0) = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.51  fof(f570,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_44),
% 0.22/0.51    inference(forward_demodulation,[],[f543,f53])).
% 0.22/0.51  fof(f543,plain,(
% 0.22/0.51    k2_relat_1(k1_xboole_0) = k1_relat_1(sK2) | ~spl3_44),
% 0.22/0.51    inference(avatar_component_clause,[],[f541])).
% 0.22/0.51  fof(f569,plain,(
% 0.22/0.51    k1_xboole_0 != k2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k2_relat_1(k1_xboole_0) = k1_relat_1(sK2)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f535,plain,(
% 0.22/0.51    spl3_42 | ~spl3_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f528,f153,f532])).
% 0.22/0.51  fof(f528,plain,(
% 0.22/0.51    k1_xboole_0 = k2_funct_1(sK2) | ~spl3_10),
% 0.22/0.51    inference(resolution,[],[f154,f57])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    v1_xboole_0(k2_funct_1(sK2)) | ~spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f153])).
% 0.22/0.51  % (20353)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f488,plain,(
% 0.22/0.51    spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f487])).
% 0.22/0.51  fof(f487,plain,(
% 0.22/0.51    $false | (spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f486,f139])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    spl3_7 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f486,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_28)),
% 0.22/0.51    inference(forward_demodulation,[],[f485,f254])).
% 0.22/0.51  fof(f485,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_9 | ~spl3_13 | ~spl3_23 | ~spl3_28)),
% 0.22/0.51    inference(forward_demodulation,[],[f484,f309])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | ~spl3_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f307])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    spl3_28 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    ~spl3_36 | spl3_8 | ~spl3_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f384,f302,f141,f399])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl3_8 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f384,plain,(
% 0.22/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_8 | ~spl3_27)),
% 0.22/0.51    inference(superposition,[],[f143,f304])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f141])).
% 0.22/0.51  fof(f374,plain,(
% 0.22/0.51    sK0 != k2_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f372,plain,(
% 0.22/0.51    spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f371])).
% 0.22/0.51  fof(f371,plain,(
% 0.22/0.51    $false | (spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f370,f143])).
% 0.22/0.51  fof(f370,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23 | ~spl3_28)),
% 0.22/0.51    inference(forward_demodulation,[],[f317,f309])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl3_9 | ~spl3_13 | ~spl3_22 | ~spl3_23)),
% 0.22/0.51    inference(forward_demodulation,[],[f316,f254])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_9 | ~spl3_13 | ~spl3_23)),
% 0.22/0.51    inference(forward_demodulation,[],[f187,f272])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_9 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f181,f170])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f146,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    spl3_28 | ~spl3_17 | ~spl3_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f314,f298,f220,f307])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    spl3_17 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.51  % (20355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f298,plain,(
% 0.22/0.51    spl3_26 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | (~spl3_17 | ~spl3_26)),
% 0.22/0.51    inference(superposition,[],[f300,f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f220])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f298])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    spl3_26 | spl3_27 | ~spl3_3 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f130,f114,f109,f302,f298])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl3_4),
% 0.22/0.51    inference(resolution,[],[f116,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    ~spl3_25 | spl3_11 | ~spl3_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f291,f278,f158,f293])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    spl3_25 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    spl3_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_relat_1(sK2)) | (spl3_11 | ~spl3_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f159])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~v1_xboole_0(sK2) | spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f158])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_relat_1(sK2)) | v1_xboole_0(sK2) | ~spl3_24),
% 0.22/0.51    inference(resolution,[],[f280,f66])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl3_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f278])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    spl3_24 | ~spl3_1 | ~spl3_6 | ~spl3_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f275,f231,f132,f87,f278])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl3_1 | ~spl3_6 | ~spl3_19)),
% 0.22/0.51    inference(forward_demodulation,[],[f274,f233])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f101,f134])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f89,f61])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    spl3_23 | ~spl3_1 | ~spl3_2 | ~spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f256,f132,f92,f87,f270])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f134])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f89])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f94,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    spl3_22 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f250,f231,f132,f92,f87,f252])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_19)),
% 0.22/0.51    inference(forward_demodulation,[],[f249,f233])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f134])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f103,f89])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f94,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    spl3_19 | ~spl3_4 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f229,f119,f114,f231])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.22/0.52    inference(forward_demodulation,[],[f126,f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f116,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    spl3_17 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f125,f114,f220])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f116,f74])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ~spl3_1 | ~spl3_6 | spl3_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    $false | (~spl3_1 | ~spl3_6 | spl3_9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f174,f147])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ~v1_funct_1(k2_funct_1(sK2)) | spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f145])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f99,f134])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f89,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl3_13 | ~spl3_1 | ~spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f166,f132,f87,f168])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f98,f134])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f89,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f145,f141,f137])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f20])).
% 0.22/0.52  fof(f20,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl3_6 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f114,f132])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f116,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f50,f119])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f114])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f109])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f49,f92])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f87])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (20346)------------------------------
% 0.22/0.52  % (20346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20346)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (20346)Memory used [KB]: 11001
% 0.22/0.52  % (20346)Time elapsed: 0.071 s
% 0.22/0.52  % (20346)------------------------------
% 0.22/0.52  % (20346)------------------------------
% 0.22/0.52  % (20360)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (20342)Success in time 0.154 s
%------------------------------------------------------------------------------
