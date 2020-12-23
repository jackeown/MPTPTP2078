%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  244 ( 619 expanded)
%              Number of leaves         :   55 ( 238 expanded)
%              Depth                    :   13
%              Number of atoms          :  750 (1956 expanded)
%              Number of equality atoms :  120 ( 337 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f107,f111,f115,f119,f123,f127,f131,f135,f148,f165,f170,f180,f189,f212,f253,f267,f354,f362,f412,f461,f482,f559,f570,f1169,f1214,f1215,f1415,f1434,f1460,f1473,f1525,f1579,f1582,f1588,f2142,f2144,f2146])).

fof(f2146,plain,
    ( ~ spl4_29
    | spl4_3
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f2145,f121,f113,f98,f352])).

fof(f352,plain,
    ( spl4_29
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f98,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f113,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f2145,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f99,f280])).

fof(f280,plain,
    ( ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f278,f114])).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f278,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_9 ),
    inference(resolution,[],[f83,f122])).

fof(f122,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f99,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f2144,plain,
    ( spl4_29
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_30
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f2104,f1413,f360,f121,f113,f352])).

fof(f360,plain,
    ( spl4_30
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1413,plain,
    ( spl4_81
  <=> ! [X4] : m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f2104,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_30
    | ~ spl4_81 ),
    inference(superposition,[],[f2083,f1590])).

fof(f1590,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f360])).

fof(f2083,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_81 ),
    inference(resolution,[],[f1409,f1414])).

fof(f1414,plain,
    ( ! [X4] : m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),k2_relat_1(sK3))))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f1413])).

fof(f1409,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X5)),sK1))) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f1344,f300])).

fof(f300,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f299,f154])).

fof(f154,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | r1_tarski(k2_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f150,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f75,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f299,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f298,f280])).

fof(f298,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f281,f114])).

fof(f281,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(resolution,[],[f85,f122])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1344,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f1232,f287])).

fof(f287,plain,
    ( ! [X6] : v1_funct_1(k7_relat_1(sK3,X6))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f168,f280])).

fof(f168,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f167,f114])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(k2_partfun1(X0,X1,sK3,X2)) )
    | ~ spl4_9 ),
    inference(resolution,[],[f84,f122])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1232,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X1))
        | m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),X2)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X1)),X2) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f195,f299])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f69,f72])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f2142,plain,
    ( ~ spl4_15
    | ~ spl4_6
    | ~ spl4_19
    | spl4_30 ),
    inference(avatar_split_clause,[],[f2140,f360,f187,f109,f157])).

fof(f157,plain,
    ( spl4_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f109,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f187,plain,
    ( spl4_19
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f2140,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_19
    | spl4_30 ),
    inference(forward_demodulation,[],[f2139,f188])).

fof(f188,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f2139,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_30 ),
    inference(trivial_inequality_removal,[],[f2138])).

fof(f2138,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_30 ),
    inference(superposition,[],[f361,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f361,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f360])).

fof(f1588,plain,
    ( ~ spl4_13
    | spl4_66
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1527,f1471,f133,f129,f121,f113,f1144,f140])).

fof(f140,plain,
    ( spl4_13
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1144,plain,
    ( spl4_66
  <=> ! [X9] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X9)
        | ~ r1_tarski(k1_xboole_0,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f129,plain,
    ( spl4_11
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f133,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1471,plain,
    ( spl4_88
  <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1527,plain,
    ( ! [X3] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X3)
        | ~ r1_tarski(k1_xboole_0,X3)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f1526,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1526,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_xboole_0,X3)
        | ~ v1_relat_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X3) )
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f1485,f130])).

fof(f130,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1485,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X3)
        | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X3) )
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_88 ),
    inference(superposition,[],[f285,f1472])).

fof(f1472,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),X1) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f172,f280])).

fof(f172,plain,
    ( ! [X4,X5] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,X4),k1_relat_1(k2_partfun1(sK0,sK1,sK3,X4)),X5)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,X4)),X5)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,X4)) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f168,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1582,plain,
    ( ~ spl4_24
    | spl4_91 ),
    inference(avatar_contradiction_clause,[],[f1580])).

fof(f1580,plain,
    ( $false
    | ~ spl4_24
    | spl4_91 ),
    inference(resolution,[],[f1578,f252])).

fof(f252,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_24
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1578,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_91 ),
    inference(avatar_component_clause,[],[f1577])).

fof(f1577,plain,
    ( spl4_91
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1579,plain,
    ( ~ spl4_91
    | spl4_62
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f1573,f1144,f1084,f1577])).

fof(f1084,plain,
    ( spl4_62
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1573,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_62
    | ~ spl4_66 ),
    inference(resolution,[],[f1524,f1145])).

fof(f1145,plain,
    ( ! [X9] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X9)
        | ~ r1_tarski(k1_xboole_0,X9) )
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f1144])).

fof(f1524,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl4_62 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1525,plain,
    ( ~ spl4_62
    | spl4_69
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1480,f1471,f1162,f1084])).

fof(f1162,plain,
    ( spl4_69
  <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f1480,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl4_69
    | ~ spl4_88 ),
    inference(superposition,[],[f1163,f1472])).

fof(f1163,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_69 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1473,plain,
    ( spl4_88
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f1469,f1458,f1471])).

fof(f1458,plain,
    ( spl4_86
  <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1469,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_86 ),
    inference(resolution,[],[f1459,f61])).

fof(f61,plain,(
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

fof(f1459,plain,
    ( v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f1460,plain,
    ( spl4_86
    | ~ spl4_10
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f1441,f1432,f125,f1458])).

fof(f125,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1432,plain,
    ( spl4_82
  <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1441,plain,
    ( v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_82 ),
    inference(resolution,[],[f1433,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f66,f126])).

fof(f126,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f1433,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1434,plain,
    ( spl4_82
    | ~ spl4_68
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1426,f1413,f1154,f1432])).

fof(f1154,plain,
    ( spl4_68
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1426,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))
    | ~ spl4_68
    | ~ spl4_81 ),
    inference(superposition,[],[f1414,f1217])).

fof(f1217,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1415,plain,
    ( ~ spl4_15
    | spl4_81
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1408,f121,f113,f1413,f157])).

fof(f1408,plain,
    ( ! [X4] :
        ( m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),k2_relat_1(sK3))))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f1344,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f1215,plain,
    ( sK0 != k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1214,plain,
    ( ~ spl4_15
    | ~ spl4_45
    | ~ spl4_19
    | spl4_68 ),
    inference(avatar_split_clause,[],[f1213,f1154,f187,f573,f157])).

fof(f573,plain,
    ( spl4_45
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1213,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_19
    | spl4_68 ),
    inference(forward_demodulation,[],[f1212,f188])).

fof(f1212,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_68 ),
    inference(trivial_inequality_removal,[],[f1211])).

fof(f1211,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_68 ),
    inference(superposition,[],[f1155,f63])).

fof(f1155,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | spl4_68 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1169,plain,
    ( ~ spl4_69
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f1168,f557,f121,f113,f95,f1162])).

fof(f95,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f557,plain,
    ( spl4_43
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1168,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f1167,f280])).

fof(f1167,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f96,f558])).

fof(f558,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f557])).

fof(f96,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f570,plain,
    ( ~ spl4_24
    | spl4_38 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | ~ spl4_24
    | spl4_38 ),
    inference(resolution,[],[f481,f252])).

fof(f481,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl4_38
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f559,plain,
    ( spl4_43
    | ~ spl4_22
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f555,f459,f210,f557])).

fof(f210,plain,
    ( spl4_22
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f459,plain,
    ( spl4_35
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f555,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_22
    | ~ spl4_35 ),
    inference(resolution,[],[f460,f211])).

fof(f211,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f460,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f459])).

fof(f482,plain,
    ( ~ spl4_38
    | ~ spl4_5
    | spl4_18 ),
    inference(avatar_split_clause,[],[f424,f184,f105,f480])).

fof(f105,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f184,plain,
    ( spl4_18
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f424,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | spl4_18 ),
    inference(superposition,[],[f185,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f185,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f461,plain,
    ( spl4_35
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f417,f109,f105,f459])).

fof(f417,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f110,f106])).

fof(f110,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f412,plain,
    ( spl4_19
    | spl4_4
    | ~ spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f398,f113,f117,f102,f187])).

fof(f102,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f117,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f398,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f318,f114])).

fof(f318,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f76,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f362,plain,
    ( ~ spl4_29
    | ~ spl4_30
    | spl4_28 ),
    inference(avatar_split_clause,[],[f357,f349,f360,f352])).

fof(f349,plain,
    ( spl4_28
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f357,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_28 ),
    inference(superposition,[],[f350,f73])).

fof(f350,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f349])).

fof(f354,plain,
    ( spl4_4
    | ~ spl4_28
    | ~ spl4_29
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f346,f121,f113,f95,f352,f349,f102])).

fof(f346,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f345,f280])).

fof(f345,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f342,f280])).

fof(f342,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f78,f96])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f267,plain,(
    ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl4_23 ),
    inference(resolution,[],[f249,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f249,plain,
    ( ! [X2,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_23
  <=> ! [X1,X2] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f253,plain,
    ( spl4_23
    | spl4_24
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f246,f129,f251,f248])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f244,f130])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f154,f60])).

fof(f212,plain,
    ( ~ spl4_13
    | spl4_22
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f208,f133,f210,f140])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f207,f134])).

fof(f207,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f200,f134])).

fof(f200,plain,(
    ! [X1] :
      ( k1_relat_1(k1_xboole_0) = X1
      | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f63,f175])).

fof(f175,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f174,f60])).

fof(f174,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | k7_relat_1(X0,X1) = X0 ) ),
    inference(global_subsumption,[],[f70,f72,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f189,plain,
    ( ~ spl4_15
    | ~ spl4_18
    | spl4_19
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f181,f178,f187,f184,f157])).

fof(f178,plain,
    ( spl4_17
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f181,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(superposition,[],[f63,f179])).

fof(f179,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( spl4_17
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f176,f113,f178])).

fof(f176,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f174,f114])).

fof(f170,plain,
    ( spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_1
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f93,f168])).

fof(f93,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f165,plain,
    ( ~ spl4_7
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl4_7
    | spl4_15 ),
    inference(subsumption_resolution,[],[f114,f163])).

fof(f163,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_15 ),
    inference(resolution,[],[f158,f72])).

fof(f158,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f148,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f146,f60])).

fof(f146,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_13 ),
    inference(resolution,[],[f141,f72])).

fof(f141,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f135,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f58,f133])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f131,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f127,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f57,f125])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f123,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f51,f121])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f47])).

fof(f47,plain,
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

% (11025)Refutation not found, incomplete strategy% (11025)------------------------------
% (11025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11025)Termination reason: Refutation not found, incomplete strategy

% (11025)Memory used [KB]: 6652
% (11025)Time elapsed: 0.135 s
% (11025)------------------------------
% (11025)------------------------------
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f119,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f52,f117])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f115,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f53,f113])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f55,f105,f102])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f98,f95,f92])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (11038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.46  % (11031)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (11039)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (11026)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (11040)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (11032)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (11037)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (11025)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (11030)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (11027)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (11028)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (11041)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (11029)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (11042)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (11043)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (11044)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (11034)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (11033)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (11035)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (11045)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (11036)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.54  % (11031)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2147,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f100,f107,f111,f115,f119,f123,f127,f131,f135,f148,f165,f170,f180,f189,f212,f253,f267,f354,f362,f412,f461,f482,f559,f570,f1169,f1214,f1215,f1415,f1434,f1460,f1473,f1525,f1579,f1582,f1588,f2142,f2144,f2146])).
% 0.22/0.54  fof(f2146,plain,(
% 0.22/0.54    ~spl4_29 | spl4_3 | ~spl4_7 | ~spl4_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f2145,f121,f113,f98,f352])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    spl4_29 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl4_9 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.54  fof(f2145,plain,(
% 0.22/0.54    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_3 | ~spl4_7 | ~spl4_9)),
% 0.22/0.54    inference(forward_demodulation,[],[f99,f280])).
% 0.22/0.54  fof(f280,plain,(
% 0.22/0.54    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.54    inference(resolution,[],[f278,f114])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f113])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_9),
% 0.22/0.54    inference(resolution,[],[f83,f122])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    v1_funct_1(sK3) | ~spl4_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f121])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f98])).
% 0.22/0.54  fof(f2144,plain,(
% 0.22/0.54    spl4_29 | ~spl4_7 | ~spl4_9 | ~spl4_30 | ~spl4_81),
% 0.22/0.54    inference(avatar_split_clause,[],[f2104,f1413,f360,f121,f113,f352])).
% 0.22/0.54  fof(f360,plain,(
% 0.22/0.54    spl4_30 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.54  fof(f1413,plain,(
% 0.22/0.54    spl4_81 <=> ! [X4] : m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),k2_relat_1(sK3))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.22/0.54  fof(f2104,plain,(
% 0.22/0.54    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_7 | ~spl4_9 | ~spl4_30 | ~spl4_81)),
% 0.22/0.54    inference(superposition,[],[f2083,f1590])).
% 0.22/0.54  fof(f1590,plain,(
% 0.22/0.54    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f360])).
% 0.22/0.54  fof(f2083,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) ) | (~spl4_7 | ~spl4_9 | ~spl4_81)),
% 0.22/0.54    inference(resolution,[],[f1409,f1414])).
% 0.22/0.54  fof(f1414,plain,(
% 0.22/0.54    ( ! [X4] : (m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),k2_relat_1(sK3))))) ) | ~spl4_81),
% 0.22/0.54    inference(avatar_component_clause,[],[f1413])).
% 0.22/0.54  fof(f1409,plain,(
% 0.22/0.54    ( ! [X6,X7,X5] : (~m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X5)),sK1)))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.54    inference(resolution,[],[f1344,f300])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.54    inference(resolution,[],[f299,f154])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k2_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.54    inference(resolution,[],[f150,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.54    inference(resolution,[],[f75,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f299,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(forward_demodulation,[],[f298,f280])).
% 0.22/0.55  fof(f298,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(resolution,[],[f281,f114])).
% 0.22/0.55  fof(f281,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 0.22/0.55    inference(resolution,[],[f85,f122])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.22/0.55  fof(f1344,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(resolution,[],[f1232,f287])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    ( ! [X6] : (v1_funct_1(k7_relat_1(sK3,X6))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(superposition,[],[f168,f280])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(resolution,[],[f167,f114])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))) ) | ~spl4_9),
% 0.22/0.55    inference(resolution,[],[f84,f122])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f1232,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~v1_funct_1(k7_relat_1(sK3,X1)) | m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),X2))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X1)),X2)) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(resolution,[],[f195,f299])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.55    inference(resolution,[],[f69,f72])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.55  fof(f2142,plain,(
% 0.22/0.55    ~spl4_15 | ~spl4_6 | ~spl4_19 | spl4_30),
% 0.22/0.55    inference(avatar_split_clause,[],[f2140,f360,f187,f109,f157])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    spl4_15 <=> v1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    spl4_6 <=> r1_tarski(sK2,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    spl4_19 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.55  fof(f2140,plain,(
% 0.22/0.55    ~r1_tarski(sK2,sK0) | ~v1_relat_1(sK3) | (~spl4_19 | spl4_30)),
% 0.22/0.55    inference(forward_demodulation,[],[f2139,f188])).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK3) | ~spl4_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f187])).
% 0.22/0.55  fof(f2139,plain,(
% 0.22/0.55    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_30),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f2138])).
% 0.22/0.55  fof(f2138,plain,(
% 0.22/0.55    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_30),
% 0.22/0.55    inference(superposition,[],[f361,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.55  fof(f361,plain,(
% 0.22/0.55    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_30),
% 0.22/0.55    inference(avatar_component_clause,[],[f360])).
% 0.22/0.55  fof(f1588,plain,(
% 0.22/0.55    ~spl4_13 | spl4_66 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_12 | ~spl4_88),
% 0.22/0.55    inference(avatar_split_clause,[],[f1527,f1471,f133,f129,f121,f113,f1144,f140])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    spl4_13 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.55  fof(f1144,plain,(
% 0.22/0.55    spl4_66 <=> ! [X9] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X9) | ~r1_tarski(k1_xboole_0,X9))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    spl4_11 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    spl4_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.55  fof(f1471,plain,(
% 0.22/0.55    spl4_88 <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 0.22/0.55  fof(f1527,plain,(
% 0.22/0.55    ( ! [X3] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X3) | ~r1_tarski(k1_xboole_0,X3) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_12 | ~spl4_88)),
% 0.22/0.55    inference(forward_demodulation,[],[f1526,f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f133])).
% 0.22/0.55  fof(f1526,plain,(
% 0.22/0.55    ( ! [X3] : (~r1_tarski(k1_xboole_0,X3) | ~v1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X3)) ) | (~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_88)),
% 0.22/0.55    inference(forward_demodulation,[],[f1485,f130])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f129])).
% 0.22/0.55  fof(f1485,plain,(
% 0.22/0.55    ( ! [X3] : (~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X3) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X3)) ) | (~spl4_7 | ~spl4_9 | ~spl4_88)),
% 0.22/0.55    inference(superposition,[],[f285,f1472])).
% 0.22/0.55  fof(f1472,plain,(
% 0.22/0.55    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_88),
% 0.22/0.55    inference(avatar_component_clause,[],[f1471])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK3,X0)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),X1)) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(superposition,[],[f172,f280])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    ( ! [X4,X5] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,X4),k1_relat_1(k2_partfun1(sK0,sK1,sK3,X4)),X5) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,X4)),X5) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,X4))) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(resolution,[],[f168,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f1582,plain,(
% 0.22/0.55    ~spl4_24 | spl4_91),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f1580])).
% 0.22/0.55  fof(f1580,plain,(
% 0.22/0.55    $false | (~spl4_24 | spl4_91)),
% 0.22/0.55    inference(resolution,[],[f1578,f252])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_24),
% 0.22/0.55    inference(avatar_component_clause,[],[f251])).
% 0.22/0.55  fof(f251,plain,(
% 0.22/0.55    spl4_24 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.55  fof(f1578,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK1) | spl4_91),
% 0.22/0.55    inference(avatar_component_clause,[],[f1577])).
% 0.22/0.55  fof(f1577,plain,(
% 0.22/0.55    spl4_91 <=> r1_tarski(k1_xboole_0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 0.22/0.55  fof(f1579,plain,(
% 0.22/0.55    ~spl4_91 | spl4_62 | ~spl4_66),
% 0.22/0.55    inference(avatar_split_clause,[],[f1573,f1144,f1084,f1577])).
% 0.22/0.55  fof(f1084,plain,(
% 0.22/0.55    spl4_62 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.22/0.55  fof(f1573,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK1) | (spl4_62 | ~spl4_66)),
% 0.22/0.55    inference(resolution,[],[f1524,f1145])).
% 0.22/0.55  fof(f1145,plain,(
% 0.22/0.55    ( ! [X9] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X9) | ~r1_tarski(k1_xboole_0,X9)) ) | ~spl4_66),
% 0.22/0.55    inference(avatar_component_clause,[],[f1144])).
% 0.22/0.55  fof(f1524,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | spl4_62),
% 0.22/0.55    inference(avatar_component_clause,[],[f1084])).
% 0.22/0.55  fof(f1525,plain,(
% 0.22/0.55    ~spl4_62 | spl4_69 | ~spl4_88),
% 0.22/0.55    inference(avatar_split_clause,[],[f1480,f1471,f1162,f1084])).
% 0.22/0.55  fof(f1162,plain,(
% 0.22/0.55    spl4_69 <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.22/0.55  fof(f1480,plain,(
% 0.22/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl4_69 | ~spl4_88)),
% 0.22/0.55    inference(superposition,[],[f1163,f1472])).
% 0.22/0.55  fof(f1163,plain,(
% 0.22/0.55    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | spl4_69),
% 0.22/0.55    inference(avatar_component_clause,[],[f1162])).
% 0.22/0.55  fof(f1473,plain,(
% 0.22/0.55    spl4_88 | ~spl4_86),
% 0.22/0.55    inference(avatar_split_clause,[],[f1469,f1458,f1471])).
% 0.22/0.55  fof(f1458,plain,(
% 0.22/0.55    spl4_86 <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 0.22/0.55  fof(f1469,plain,(
% 0.22/0.55    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_86),
% 0.22/0.55    inference(resolution,[],[f1459,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f1459,plain,(
% 0.22/0.55    v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) | ~spl4_86),
% 0.22/0.55    inference(avatar_component_clause,[],[f1458])).
% 0.22/0.55  fof(f1460,plain,(
% 0.22/0.55    spl4_86 | ~spl4_10 | ~spl4_82),
% 0.22/0.55    inference(avatar_split_clause,[],[f1441,f1432,f125,f1458])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    spl4_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.55  fof(f1432,plain,(
% 0.22/0.55    spl4_82 <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 0.22/0.55  fof(f1441,plain,(
% 0.22/0.55    v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) | (~spl4_10 | ~spl4_82)),
% 0.22/0.55    inference(resolution,[],[f1433,f151])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl4_10),
% 0.22/0.55    inference(resolution,[],[f66,f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0) | ~spl4_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f125])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.22/0.55  fof(f1433,plain,(
% 0.22/0.55    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) | ~spl4_82),
% 0.22/0.55    inference(avatar_component_clause,[],[f1432])).
% 0.22/0.55  fof(f1434,plain,(
% 0.22/0.55    spl4_82 | ~spl4_68 | ~spl4_81),
% 0.22/0.55    inference(avatar_split_clause,[],[f1426,f1413,f1154,f1432])).
% 0.22/0.55  fof(f1154,plain,(
% 0.22/0.55    spl4_68 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.22/0.55  fof(f1426,plain,(
% 0.22/0.55    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) | (~spl4_68 | ~spl4_81)),
% 0.22/0.55    inference(superposition,[],[f1414,f1217])).
% 0.22/0.55  fof(f1217,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | ~spl4_68),
% 0.22/0.55    inference(avatar_component_clause,[],[f1154])).
% 0.22/0.55  fof(f1415,plain,(
% 0.22/0.55    ~spl4_15 | spl4_81 | ~spl4_7 | ~spl4_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f1408,f121,f113,f1413,f157])).
% 0.22/0.55  fof(f1408,plain,(
% 0.22/0.55    ( ! [X4] : (m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),k2_relat_1(sK3)))) | ~v1_relat_1(sK3)) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(resolution,[],[f1344,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.22/0.55  fof(f1215,plain,(
% 0.22/0.55    sK0 != k1_relat_1(sK3) | r1_tarski(k1_xboole_0,sK0) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK3))),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f1214,plain,(
% 0.22/0.55    ~spl4_15 | ~spl4_45 | ~spl4_19 | spl4_68),
% 0.22/0.55    inference(avatar_split_clause,[],[f1213,f1154,f187,f573,f157])).
% 0.22/0.55  fof(f573,plain,(
% 0.22/0.55    spl4_45 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.22/0.55  fof(f1213,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK0) | ~v1_relat_1(sK3) | (~spl4_19 | spl4_68)),
% 0.22/0.55    inference(forward_demodulation,[],[f1212,f188])).
% 0.22/0.55  fof(f1212,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_68),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f1211])).
% 0.22/0.55  fof(f1211,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_68),
% 0.22/0.55    inference(superposition,[],[f1155,f63])).
% 0.22/0.55  fof(f1155,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | spl4_68),
% 0.22/0.55    inference(avatar_component_clause,[],[f1154])).
% 0.22/0.55  fof(f1169,plain,(
% 0.22/0.55    ~spl4_69 | spl4_2 | ~spl4_7 | ~spl4_9 | ~spl4_43),
% 0.22/0.55    inference(avatar_split_clause,[],[f1168,f557,f121,f113,f95,f1162])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f557,plain,(
% 0.22/0.55    spl4_43 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.55  fof(f1168,plain,(
% 0.22/0.55    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_7 | ~spl4_9 | ~spl4_43)),
% 0.22/0.55    inference(forward_demodulation,[],[f1167,f280])).
% 0.22/0.55  fof(f1167,plain,(
% 0.22/0.55    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_43)),
% 0.22/0.55    inference(forward_demodulation,[],[f96,f558])).
% 0.22/0.55  fof(f558,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl4_43),
% 0.22/0.55    inference(avatar_component_clause,[],[f557])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f95])).
% 0.22/0.55  fof(f570,plain,(
% 0.22/0.55    ~spl4_24 | spl4_38),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f567])).
% 0.22/0.55  fof(f567,plain,(
% 0.22/0.55    $false | (~spl4_24 | spl4_38)),
% 0.22/0.55    inference(resolution,[],[f481,f252])).
% 0.22/0.55  fof(f481,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | spl4_38),
% 0.22/0.55    inference(avatar_component_clause,[],[f480])).
% 0.22/0.55  fof(f480,plain,(
% 0.22/0.55    spl4_38 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.55  fof(f559,plain,(
% 0.22/0.55    spl4_43 | ~spl4_22 | ~spl4_35),
% 0.22/0.55    inference(avatar_split_clause,[],[f555,f459,f210,f557])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    spl4_22 <=> ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.55  fof(f459,plain,(
% 0.22/0.55    spl4_35 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.55  fof(f555,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | (~spl4_22 | ~spl4_35)),
% 0.22/0.55    inference(resolution,[],[f460,f211])).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl4_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f210])).
% 0.22/0.55  fof(f460,plain,(
% 0.22/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl4_35),
% 0.22/0.55    inference(avatar_component_clause,[],[f459])).
% 0.22/0.55  fof(f482,plain,(
% 0.22/0.55    ~spl4_38 | ~spl4_5 | spl4_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f424,f184,f105,f480])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    spl4_5 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    spl4_18 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.55  fof(f424,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | spl4_18)),
% 0.22/0.55    inference(superposition,[],[f185,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl4_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f105])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    ~r1_tarski(sK0,k1_relat_1(sK3)) | spl4_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f184])).
% 0.22/0.55  fof(f461,plain,(
% 0.22/0.55    spl4_35 | ~spl4_5 | ~spl4_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f417,f109,f105,f459])).
% 0.22/0.55  fof(f417,plain,(
% 0.22/0.55    r1_tarski(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_6)),
% 0.22/0.55    inference(superposition,[],[f110,f106])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    r1_tarski(sK2,sK0) | ~spl4_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f109])).
% 0.22/0.55  fof(f412,plain,(
% 0.22/0.55    spl4_19 | spl4_4 | ~spl4_8 | ~spl4_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f398,f113,f117,f102,f187])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    spl4_4 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    spl4_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.55  fof(f398,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK3) | ~spl4_7),
% 0.22/0.55    inference(resolution,[],[f318,f114])).
% 0.22/0.55  fof(f318,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f315])).
% 0.22/0.55  fof(f315,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.55    inference(superposition,[],[f76,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f362,plain,(
% 0.22/0.55    ~spl4_29 | ~spl4_30 | spl4_28),
% 0.22/0.55    inference(avatar_split_clause,[],[f357,f349,f360,f352])).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    spl4_28 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.55  fof(f357,plain,(
% 0.22/0.55    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_28),
% 0.22/0.55    inference(superposition,[],[f350,f73])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_28),
% 0.22/0.55    inference(avatar_component_clause,[],[f349])).
% 0.22/0.55  fof(f354,plain,(
% 0.22/0.55    spl4_4 | ~spl4_28 | ~spl4_29 | spl4_2 | ~spl4_7 | ~spl4_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f346,f121,f113,f95,f352,f349,f102])).
% 0.22/0.55  fof(f346,plain,(
% 0.22/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | (spl4_2 | ~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(forward_demodulation,[],[f345,f280])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(forward_demodulation,[],[f342,f280])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_2),
% 0.22/0.55    inference(resolution,[],[f78,f96])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f50])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    ~spl4_23),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f266])).
% 0.22/0.55  fof(f266,plain,(
% 0.22/0.55    $false | ~spl4_23),
% 0.22/0.55    inference(resolution,[],[f249,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.55  fof(f249,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_23),
% 0.22/0.55    inference(avatar_component_clause,[],[f248])).
% 0.22/0.55  fof(f248,plain,(
% 0.22/0.55    spl4_23 <=> ! [X1,X2] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    spl4_23 | spl4_24 | ~spl4_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f246,f129,f251,f248])).
% 0.22/0.55  fof(f246,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_11),
% 0.22/0.55    inference(forward_demodulation,[],[f244,f130])).
% 0.22/0.55  fof(f244,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.55    inference(resolution,[],[f154,f60])).
% 0.22/0.55  fof(f212,plain,(
% 0.22/0.55    ~spl4_13 | spl4_22 | ~spl4_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f208,f133,f210,f140])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1 | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_12),
% 0.22/0.55    inference(forward_demodulation,[],[f207,f134])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_12),
% 0.22/0.55    inference(forward_demodulation,[],[f200,f134])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    ( ! [X1] : (k1_relat_1(k1_xboole_0) = X1 | ~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f63,f175])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f174,f60])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    ( ! [X4,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | k7_relat_1(X0,X1) = X0) )),
% 0.22/0.55    inference(global_subsumption,[],[f70,f72,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    ~spl4_15 | ~spl4_18 | spl4_19 | ~spl4_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f181,f178,f187,f184,f157])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    spl4_17 <=> sK3 = k7_relat_1(sK3,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_17),
% 0.22/0.55    inference(superposition,[],[f63,f179])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    sK3 = k7_relat_1(sK3,sK0) | ~spl4_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f178])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    spl4_17 | ~spl4_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f176,f113,f178])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    sK3 = k7_relat_1(sK3,sK0) | ~spl4_7),
% 0.22/0.55    inference(resolution,[],[f174,f114])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    spl4_1 | ~spl4_7 | ~spl4_9),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f169])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    $false | (spl4_1 | ~spl4_7 | ~spl4_9)),
% 0.22/0.55    inference(subsumption_resolution,[],[f93,f168])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    ~spl4_7 | spl4_15),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f164])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    $false | (~spl4_7 | spl4_15)),
% 0.22/0.55    inference(subsumption_resolution,[],[f114,f163])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_15),
% 0.22/0.55    inference(resolution,[],[f158,f72])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | spl4_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f157])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    spl4_13),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f147])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    $false | spl4_13),
% 0.22/0.55    inference(resolution,[],[f146,f60])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_13),
% 0.22/0.55    inference(resolution,[],[f141,f72])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ~v1_relat_1(k1_xboole_0) | spl4_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f140])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    spl4_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f58,f133])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    spl4_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f59,f129])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    spl4_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f57,f125])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    spl4_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f51,f121])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  % (11025)Refutation not found, incomplete strategy% (11025)------------------------------
% 0.22/0.55  % (11025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11025)Memory used [KB]: 6652
% 0.22/0.55  % (11025)Time elapsed: 0.135 s
% 0.22/0.55  % (11025)------------------------------
% 0.22/0.55  % (11025)------------------------------
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.55    inference(negated_conjecture,[],[f20])).
% 0.22/0.55  fof(f20,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    spl4_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f52,f117])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    spl4_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f53,f113])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    spl4_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f54,f109])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    r1_tarski(sK2,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ~spl4_4 | spl4_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f55,f105,f102])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f56,f98,f95,f92])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11031)------------------------------
% 0.22/0.55  % (11031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11031)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11031)Memory used [KB]: 12025
% 0.22/0.55  % (11031)Time elapsed: 0.125 s
% 0.22/0.55  % (11031)------------------------------
% 0.22/0.55  % (11031)------------------------------
% 0.22/0.55  % (11024)Success in time 0.187 s
%------------------------------------------------------------------------------
